import { DEFINITION_KINDS } from "./declaration-model.js";
import { MAP_NODE_COLORS } from "./graph-style.js";
import { createMapNavigation } from "./map-navigation.js";
import { createMapScene } from "./map-scene.js";
import { createMapHeader } from "./map-header.js";
import { ZOOM_STEP, canAnimateCamera, createCameraFrames, zoomFactorForKey, zoomFactorForWheel } from "./map-zoom.js";
import { declarationRelations, declarationSourceLink, declarationStatement } from "./declaration-details.js";

const width = 960;
const height = 670;
const categories = [
  ["Theorems", MAP_NODE_COLORS.blue, (entry) => entry.kind === "theorem"],
  ["Definitions", MAP_NODE_COLORS.green, (entry) => DEFINITION_KINDS.has(entry.kind)],
  ["Other declarations", "#dfbd86", () => true],
];

function element(tag, className, text = "") {
  const node = document.createElement(tag);
  node.className = className;
  node.textContent = text;
  return node;
}

function button(text, action, className = "") {
  const control = element("button", className, text);
  control.type = "button";
  control.addEventListener("click", action);
  return control;
}

export function renderResearchMap(children, onOpenDeclaration, onRegionChange, overviewHeader, rootName, hierarchy, mapCounts, selectedName, initialModule, onMapStateChange) {
  const section = element("section", "research-map explorer-map-theme explorer-map-frame");
  const { header, heading, status: declarationCount } = createMapHeader(rootName);
  const controlsSlot = element("div", "map-controls-slot");
  heading.id = "research-map-title";
  section.setAttribute("aria-labelledby", heading.id);
  const legend = element("ul", "research-map-legend");
  for (const [label, color] of categories) {
    const item = element("li", "");
    const dot = element("i", "");
    dot.style.backgroundColor = color;
    dot.setAttribute("aria-hidden", "true");
    item.append(dot, document.createTextNode(label));
    legend.append(item);
  }
  const controls = element("div", "research-map-controls graph-view-controls");
  const stage = element("div", "research-map-stage explorer-map-stage");
  const canvas = element("canvas", "");
  canvas.width = width * 2;
  canvas.height = height * 2;
  canvas.tabIndex = 0;
  canvas.setAttribute("aria-label", "Declaration map. Arrow keys pan, plus and minus zoom, zero resets. Use the declaration picker to open a point.");
  const ctx = canvas.getContext("2d");
  const detail = element("section", "research-map-detail");
  detail.hidden = true;
  const hint = "Choose a region to zoom in.";
  const preview = element("p", "research-map-preview", hint);
  preview.setAttribute("aria-live", "off");
  const picker = element("label", "research-map-picker");
  const caption = element("span", "", "Declaration");
  const select = element("select", "");
  picker.append(caption, select);
  const scene = createMapScene(children, hierarchy, width, height);
  const { allRegions, points } = scene;
  const labels = new Map(allRegions.map((region) => [region, makeLabel(region)]));
  const colors = new Map(points.map((point) => [point, categories.find(([, , matches]) => matches(point.entry))[1]]));

  function makeLabel(region) {
    const { name } = region;
    const label = button(name, () => openRegion(region), "research-map-region");
    label.disabled = region.points.length === 0;
    label.setAttribute("aria-label", `${name}, ${region.points.length} declarations`);
    return label;
  }
  function showDeclarationCount({ definitions, proved, missingAxiomData }) {
    const totals = [
      `${definitions.toLocaleString("en")} definition${definitions === 1 ? "" : "s"}`,
      `${proved.toLocaleString("en")} proved theorem${proved === 1 ? "" : "s"}`,
    ];
    if (missingAxiomData) {
      totals.push(`${missingAxiomData.toLocaleString("en")} theorem${missingAxiomData === 1 ? "" : "s"} without axiom data`);
    }
    declarationCount.textContent = totals.join(" · ");
  }
  showDeclarationCount(mapCounts);
  const connectionDetails = element("details", "research-map-connections");
  let shownBundles;
  function showConnectionCounts(connections, title) {
    if (shownBundles === connections) return;
    shownBundles = connections;
    connectionDetails.hidden = connections.length === 0;
    const list = element("ul", "");
    for (const { a, b, ab, ba } of connections) {
      const directions = [];
      if (ab) directions.push(`${a.name} → ${b.name}: ${ab.toLocaleString("en")}`);
      if (ba) directions.push(`${b.name} → ${a.name}: ${ba.toLocaleString("en")}`);
      list.append(element("li", "", directions.join(" · ")));
    }
    connectionDetails.replaceChildren(element("summary", "", title), list);
  }
  const navigation = createMapNavigation(width, height);
  const { screen, pointOnScreen } = navigation;
  const parentControl = button("Parent region", () => { if (navigation.active?.parent) openRegion(navigation.active.parent); });
  parentControl.hidden = true;
  let hovered = null;
  const hoverLabel = element("div", "research-map-hover");
  hoverLabel.hidden = true;
  hoverLabel.setAttribute("aria-hidden", "true");
  let drag = null;
  const camera = createCameraFrames();

  function animateCamera() {
    if (navigation.animating) camera.start(stepCamera);
    else camera.stop();
  }

  function stepCamera(now) {
    if (!section.isConnected || section.closest("[hidden]")) {
      navigation.stop();
      return false;
    }
    navigation.step(now);
    draw();
    return navigation.animating;
  }

  function stopCamera() {
    navigation.stop();
    animateCamera();
  }

  function line(from, to, color) {
    const [x, y] = pointOnScreen(from);
    const [tx, ty] = pointOnScreen(to);
    const angle = Math.atan2(ty - y, tx - x);
    const endX = tx - 7 * Math.cos(angle);
    const endY = ty - 7 * Math.sin(angle);
    ctx.strokeStyle = color;
    ctx.beginPath();
    ctx.moveTo(x, y);
    ctx.lineTo(endX, endY);
    ctx.lineTo(endX - 7 * Math.cos(angle - .5), endY - 7 * Math.sin(angle - .5));
    ctx.moveTo(endX, endY);
    ctx.lineTo(endX - 7 * Math.cos(angle + .5), endY - 7 * Math.sin(angle + .5));
    ctx.stroke();
  }

  function placeLabels(frame) {
    const visible = new Set(frame.labels);
    for (const [region, label] of labels) label.hidden = !visible.has(region);
    const stageWidth = stage.clientWidth;
    const stageHeight = stage.clientHeight;
    const measured = frame.labels.map((region) => {
      const label = labels.get(region);
      return { region, label, w: label.offsetWidth, h: label.offsetHeight };
    });
    const placed = [];
    for (const { region, label, w, h } of measured) {
      const [x, y] = screen(region.x, region.y + region.radius);
      if (!stageWidth || !stageHeight) continue;
      const anchorX = x / width * stageWidth;
      const anchorY = y / height * stageHeight;
      const [, above] = screen(region.x, region.y - region.radius);
      const candidates = [anchorY + 6, above / height * stageHeight - h - 6, anchorY + h + 10];
      const center = Math.max(w / 2 + 4, Math.min(stageWidth - w / 2 - 4, anchorX));
      const left = center - w / 2;
      const top = candidates.map((value) => Math.max(4, Math.min(stageHeight - h - 4, value)))
        .find((value) => placed.every((box) => left >= box.right + 4 || left + w + 4 <= box.left ||
          value >= box.bottom + 4 || value + h + 4 <= box.top));
      label.hidden = top === undefined;
      if (top === undefined) continue;
      label.style.left = `${center}px`;
      label.style.top = `${top}px`;
      placed.push({ left, right: left + w, top, bottom: top + h });
    }
  }

  function draw() {
    const { selected, view, overview } = navigation;
    const frame = scene.frame(navigation);
    hoverLabel.hidden = !hovered;
    if (hovered) {
      const [x, y] = pointOnScreen(hovered);
      hoverLabel.textContent = hovered.entry.name;
      const halfLabel = hoverLabel.offsetWidth / 2 + 6;
      const left = x / width * stage.clientWidth;
      const top = y / height * stage.clientHeight + 12;
      hoverLabel.style.left = `${Math.max(halfLabel, Math.min(stage.clientWidth - halfLabel, left))}px`;
      hoverLabel.style.top = `${Math.max(4, Math.min(stage.clientHeight - hoverLabel.offsetHeight - 4, top))}px`;
    }
    canvas.style.touchAction = view.zoom > 1.5 ? "none" : "pan-y";
    placeLabels(frame);
    const visibleBundles = frame.bundles;
    showConnectionCounts(visibleBundles, overview ? "Dependencies between regions" : "Dependencies between submodules");
    if (!ctx) return;
    ctx.setTransform(2, 0, 0, 2, 0, 0);
    ctx.clearRect(0, 0, width, height);
    if (visibleBundles.length) {
      ctx.strokeStyle = "rgba(170, 199, 188, .33)";
      ctx.lineCap = "round";
      for (const { a, b, ab, ba } of visibleBundles) {
        const angle = Math.atan2(b.y - a.y, b.x - a.x);
        const dx = Math.cos(angle);
        const dy = Math.sin(angle);
        ctx.lineWidth = 1 + Math.log10(ab + ba + 1) * 2;
        ctx.beginPath();
        const gap = 6 / view.zoom;
        ctx.moveTo(...screen(a.x + dx * (a.radius + gap), a.y + dy * (a.radius + gap)));
        ctx.lineTo(...screen(b.x - dx * (b.radius + gap), b.y - dy * (b.radius + gap)));
        ctx.stroke();
      }
      ctx.lineCap = "butt";
      ctx.lineWidth = 1;
    }
    for (const region of frame.outlines) {
      ctx.strokeStyle = "#42605a";
      ctx.beginPath();
      ctx.arc(...screen(region.x, region.y), region.radius * view.zoom + 5, 0, 2 * Math.PI);
      ctx.stroke();
    }
    const nearby = new Set();
    if (selected) {
      for (const [names, incoming, color] of [
        [selected.entry.dependencies, false, "#8dceb1"],
        [selected.entry.dependents, true, "#90bed2"],
      ]) {
        for (const name of names ?? []) {
          const point = scene.point(name);
          if (!point || point === selected) continue;
          nearby.add(point);
          line(incoming ? point : selected, incoming ? selected : point, color);
        }
      }
    }
    for (const [, color] of categories) {
      ctx.fillStyle = color;
      ctx.beginPath();
      for (const point of points) {
        if (colors.get(point) !== color || (selected && point === selected)) continue;
        const [x, y] = pointOnScreen(point);
        if (x < -8 || x > width + 8 || y < -8 || y > height + 8) continue;
        const r = nearby.has(point) ? 4 : Math.min(3, 1.35 + view.zoom * .15);
        ctx.moveTo(x + r, y);
        ctx.arc(x, y, r, 0, 2 * Math.PI);
      }
      ctx.globalAlpha = selected ? .55 : .92;
      ctx.fill();
    }
    ctx.globalAlpha = 1;
    if (selected) {
      ctx.fillStyle = "#ffffff";
      ctx.beginPath();
      ctx.arc(...pointOnScreen(selected), 5, 0, 2 * Math.PI);
      ctx.fill();
    }
    if (hovered) {
      ctx.strokeStyle = "#edf5ee";
      ctx.beginPath();
      ctx.arc(...pointOnScreen(hovered), 7, 0, 2 * Math.PI);
      ctx.stroke();
    }
  }

  function populatePicker(region) {
    const candidates = region?.points ?? sortedPoints;
    caption.textContent = region ? `Declaration in ${region.name}` : "Declaration across all regions";
    select.disabled = candidates.length === 0;
    const placeholder = element("option", "", candidates.length ? "Choose a declaration" : "No matching declarations");
    placeholder.value = "";
    placeholder.disabled = true;
    select.replaceChildren(placeholder, ...candidates.map(({ entry }) => {
      const option = element("option", "", entry.name);
      option.value = entry.name;
      return option;
    }));
    select.value = "";
  }

  function updateRegion(previous) {
    const region = navigation.active;
    if (previous === region) return;
    heading.textContent = region?.name ?? rootName;
    showDeclarationCount(region?.module.visibleCounts ?? mapCounts);
    onRegionChange(region?.moduleName ?? null, browseMap);
    parentControl.hidden = !region?.parent;
    populatePicker(region);
  }

  function publishSelection() {
    onMapStateChange?.({
      moduleName: navigation.active?.moduleName ?? null,
      selectedName: navigation.selected?.entry.name ?? null,
    });
  }

  function reset(animate = canAnimateCamera()) {
    hovered = null;
    const previous = navigation.active;
    navigation.reset(animate);
    animateCamera();
    updateRegion(previous);
    detail.hidden = true;
    select.value = "";
    preview.textContent = hint;
    draw();
  }

  function browseMap(moduleName) {
    if (moduleName === "LeanCondensedMatter") {
      reset();
      publishSelection();
      return;
    }
    const region = scene.region(moduleName);
    if (region) openRegion(region);
  }

  function clearSelection() {
    detail.hidden = true;
    select.value = "";
    const region = navigation.active;
    preview.textContent = !region ? hint : region.children.length
      ? "Choose a submodule or select a declaration." : "Select a dot or choose a declaration.";
  }

  function openRegion(region, initial = false) {
    if (!region.points.length) return;
    hovered = null;
    const previous = navigation.active;
    navigation.open(region, !initial && canAnimateCamera());
    updateRegion(previous);
    clearSelection();
    animateCamera();
    draw();
    if (!initial) canvas.focus?.({ preventScroll: true });
    if (!initial) publishSelection();
  }

  function relation(title, names) {
    const block = element("ul", "research-map-relations");
    const { entries, availableCount } = declarationRelations(names, (name) => Boolean(scene.point(name)));
    const count = availableCount === entries.length ? String(entries.length) : `${entries.length} total, ${availableCount} on map`;
    const summary = element("summary", "", `${title} (${count})`);
    const list = element("details", "research-map-relation");
    list.open = availableCount > 0 && availableCount <= 5;
    list.append(summary, block);
    for (const { name, available } of entries) {
      if (!available) continue;
      const item = element("li", "");
      const link = button(name.split(".").at(-1), () => openPoint(scene.point(name), true), "research-map-related");
      link.title = name;
      link.setAttribute("aria-label", `Show ${name} on the map`);
      const namespace = element("small", "", name.split(".").slice(0, -1).join("."));
      if (namespace.textContent) link.append(namespace);
      item.append(link);
      block.append(item);
    }
    if (entries.length && !availableCount) list.append(element("p", "muted", "No related declarations match this map."));
    return list;
  }

  function openPoint(point, focusDetail = false) {
    if (!point) return;
    hovered = null;
    const previous = navigation.active;
    navigation.select(point);
    animateCamera();
    updateRegion(previous);
    select.value = point.entry.name;
    const head = element("header", "research-map-detail-header");
    const title = element("h3", "research-map-detail-title", point.entry.name);
    title.tabIndex = -1;
    const graph = button("View dependency graph", () => onOpenDeclaration(point.entry.name, { fromMap: true }),
      "focus-button research-map-open-graph");
    head.append(title, graph);
    const source = declarationSourceLink(point.entry);
    if (source) head.append(source);
    detail.replaceChildren(head, ...declarationStatement(point.entry),
      relation("Depends on", point.entry.dependencies),
      relation("Used by", point.entry.dependents));
    detail.hidden = false;
    draw();
    if (focusDetail) {
      publishSelection();
      title.focus?.({ preventScroll: true });
      title.scrollIntoView?.({ block: "start" });
    }
  }

  function zoomBy(factor, x, y) {
    const previous = navigation.active;
    if (!navigation.zoom(factor, x, y, canAnimateCamera())) return;
    hovered = null;
    updateRegion(previous);
    if (navigation.active !== previous) {
      clearSelection();
      publishSelection();
    }
    animateCamera();
    draw();
  }

  function coords(event) {
    const rect = canvas.getBoundingClientRect();
    return [(event.clientX - rect.left) * width / rect.width, (event.clientY - rect.top) * height / rect.height];
  }

  canvas.addEventListener("pointerdown", (event) => {
    if (!event.isPrimary || event.button !== 0 || (event.pointerType === "touch" && navigation.overview)) return;
    stopCamera();
    if (hovered) {
      hovered = null;
      draw();
    }
    drag = { id: event.pointerId, start: coords(event), view: { ...navigation.view }, moved: false };
    canvas.setPointerCapture(event.pointerId);
  });
  canvas.addEventListener("pointermove", (event) => {
    const [x, y] = coords(event);
    if (drag?.id === event.pointerId) {
      const dx = x - drag.start[0];
      const dy = y - drag.start[1];
      if (!drag.moved && Math.hypot(dx, dy) < 7) return;
      if (!drag.moved) canvas.classList.add("is-dragging");
      drag.moved = true;
      navigation.pan(-dx, -dy, drag.view);
      draw();
    } else if (event.pointerType !== "touch" && !camera.running) {
      const point = scene.frame(navigation).hoverPoint(x, y);
      if (point !== hovered) {
        hovered = point;
        draw();
      }
    }
  });
  canvas.addEventListener("pointerleave", () => {
    if (!hovered) return;
    hovered = null;
    draw();
  });
  for (const type of ["pointerup", "pointercancel", "lostpointercapture"]) {
    canvas.addEventListener(type, (event) => {
      if (drag?.id !== event.pointerId) return;
      canvas.classList.remove("is-dragging");
      if (type === "pointercancel") drag = null;
    });
  }
  canvas.addEventListener("click", (event) => {
    if (drag?.moved) { drag = null; return; }
    drag = null;
    const [x, y] = coords(event);
    const target = scene.frame(navigation).target(x, y);
    if (target?.region) openRegion(target.region);
    else if (target?.point) openPoint(target.point, true);
  });
  canvas.addEventListener("wheel", (event) => {
    const factor = zoomFactorForWheel(event);
    if (!factor) return;
    event.preventDefault();
    zoomBy(factor, ...coords(event));
  }, { passive: false });
  canvas.addEventListener("keydown", (event) => {
    const shift = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, -1], ArrowDown: [0, 1] }[event.key];
    if (shift) {
      stopCamera();
      hovered = null;
      navigation.pan(shift[0] * 70, shift[1] * 70);
      draw();
    } else if (event.key === "0" || event.key === "Escape") {
      reset();
      publishSelection();
    }
    else {
      const factor = zoomFactorForKey(event.key);
      if (!factor) return;
      zoomBy(factor);
    }
    event.preventDefault();
  });
  select.addEventListener("change", () => openPoint(scene.point(select.value), true));
  const zoomOut = button("−", () => zoomBy(1 / ZOOM_STEP), "map-zoom-button");
  zoomOut.setAttribute("aria-label", "Zoom out");
  const zoomIn = button("+", () => zoomBy(ZOOM_STEP), "map-zoom-button");
  zoomIn.setAttribute("aria-label", "Zoom in");
  controls.append(parentControl, zoomOut, zoomIn, button("Whole map", () => {
    reset();
    publishSelection();
  }));
  stage.append(canvas, ...labels.values(), hoverLabel);
  const overviewFooter = element("div", "research-map-overview");
  overviewFooter.append(...overviewHeader);
  section.append(header, controls, stage, controlsSlot, legend, preview, picker, detail, connectionDetails, overviewFooter);
  const sortedPoints = [...points].sort((a, b) => a.entry.name.localeCompare(b.entry.name));
  populatePicker(null);
  reset(false);
  onRegionChange(null, browseMap);
  const initialRegion = initialModule && scene.region(initialModule);
  if (initialRegion) openRegion(initialRegion, true);
  else if (initialModule && initialModule !== rootName) {
    preview.textContent = `No declarations in ${initialModule} match the current filters. Showing the whole map.`;
  }
  if (selectedName) openPoint(scene.point(selectedName));
  let resizeObserver;
  return {
    element: section,
    mount() {
      draw();
      if (typeof ResizeObserver === "function") {
        resizeObserver = new ResizeObserver(draw);
        resizeObserver.observe(stage);
      } else window.addEventListener?.("resize", draw);
    },
    dispose() {
      stopCamera();
      resizeObserver?.disconnect();
      window.removeEventListener?.("resize", draw);
    },
  };
}
