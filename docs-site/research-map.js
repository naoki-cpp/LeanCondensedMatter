import { DEFINITION_KINDS } from "./declaration-model.js";
import { MAP_NODE_COLORS } from "./graph-style.js";
import { createMapNavigation } from "./map-navigation.js";
import { createMapHeader } from "./map-header.js";
import { ZOOM_STEP, canAnimateCamera, zoomFactorForKey, zoomFactorForWheel } from "./map-zoom.js";
import { renderStatement } from "./statement-view.js";

const width = 960;
const height = 670;
const goldenAngle = Math.PI * (3 - Math.sqrt(5));
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

export function renderResearchMap(children, onOpenDeclaration, onRegionChange, overviewHeader, rootName, hierarchy, mapCounts, selectedName) {
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
  const byName = new Map();
  const largest = Math.max(1, ...children.map((child) => child.entries.length));
  const columns = Math.min(3, Math.max(1, children.length));
  const rows = Math.max(1, Math.ceil(children.length / columns));
  const spacing = Math.min(91, (height / rows - 46) / 2);
  const allRegions = [];
  const regionByModule = new Map();
  function placeCloud(points, scope, x, y, radius) {
    points.forEach((point, i) => {
      const distance = radius * .94 * Math.sqrt(i / points.length);
      const angle = goldenAngle * i;
      point.positions.set(scope, { x: x + distance * Math.cos(angle), y: y + distance * Math.sin(angle) });
    });
  }
  function buildRegion(module, x, y, radius, parent = null) {
    const name = module.name.replace(/([a-z])([A-Z])/g, "$1 $2");
    const region = { name, moduleName: module.path, module, x, y, radius, parent, children: [] };
    allRegions.push(region);
    regionByModule.set(module, region);
    const ordered = [...module.children].sort(([a], [b]) => a.localeCompare(b));
    if (module.declarations.length) ordered.unshift(["", null]);
    const cellColumns = Math.max(1, Math.ceil(Math.sqrt(ordered.length)));
    const cellRows = Math.ceil(ordered.length / cellColumns);
    const cell = region.radius * Math.SQRT2 / Math.max(cellColumns, cellRows);
    region.points = ordered.flatMap(([key, childModule], i) => {
      const grouped = ordered.length > 1;
      const gx = grouped ? x + ((i % cellColumns) - (cellColumns - 1) / 2) * cell : x;
      const gy = grouped ? y + (Math.floor(i / cellColumns) - (cellRows - 1) / 2) * cell : y;
      const groupRadius = grouped ? cell * .34 : region.radius * .75;
      let points;
      if (key) {
        const child = buildRegion(childModule, gx, gy, groupRadius, region);
        region.children.push(child);
        points = child.points;
      } else {
        points = module.declarations.map((entry) => {
          const point = { entry, region, positions: new Map(), color: categories.find(([, , matches]) => matches(entry))[1] };
          byName.set(entry.name, point);
          return point;
        });
      }
      placeCloud(points, region, gx, gy, groupRadius);
      if (!key) for (const point of points) Object.assign(point, point.positions.get(region));
      return points;
    });
    region.label = makeLabel(region);
    return region;
  }
  const regions = children.map((child, index) => {
    const x = ((index % columns) + .5) * width / columns + (Math.floor(index / columns) % 2 ? 20 : -20);
    const y = (Math.floor(index / columns) + .44) * height / rows;
    const radius = spacing * Math.sqrt(child.entries.length / largest);
    const region = buildRegion(child, x, y, radius);
    placeCloud(region.points, null, x, y, radius);
    return region;
  });

  function makeLabel(region) {
    const { name } = region;
    const label = button(name, () => openRegion(region), "research-map-region");
    label.disabled = region.points.length === 0;
    label.setAttribute("aria-label", `${name}, ${region.points.length} declarations`);
    return label;
  }
  const points = [...byName.values()];
  function showDeclarationCount({ definitions, proved }) {
    declarationCount.textContent = `${definitions.toLocaleString("en")} definition${definitions === 1 ? "" : "s"} · ${proved.toLocaleString("en")} proved theorem${proved === 1 ? "" : "s"}`;
  }
  showDeclarationCount(mapCounts);
  const bundleCache = new Map();
  function bundlesFor(module) {
    if (!module) return emptyBundles;
    if (!bundleCache.has(module)) {
      bundleCache.set(module, hierarchy.bundles(module).map(({ a, b, ab, ba }) => ({
        a: regionByModule.get(a), b: regionByModule.get(b), ab, ba,
      })));
    }
    return bundleCache.get(module);
  }
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
  let cameraFrame = null;

  function animateCamera() {
    if (cameraFrame !== null) cancelAnimationFrame(cameraFrame);
    cameraFrame = navigation.animating ? requestAnimationFrame(stepCamera) : null;
  }

  function stepCamera(now) {
    cameraFrame = null;
    if (!section.isConnected) { navigation.stop(); return; }
    navigation.step(now);
    draw();
    animateCamera();
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

  function placeLabels() {
    const { active, overview } = navigation;
    const visible = [];
    for (const region of allRegions) {
      region.label.hidden = !overview && active
        ? region.parent !== active
        : Boolean(region.parent);
      if (!region.label.hidden) visible.push(region);
    }
    const stageWidth = stage.clientWidth;
    const stageHeight = stage.clientHeight;
    const measured = visible.map((region) => ({
      region, w: region.label.offsetWidth, h: region.label.offsetHeight,
    }));
    const placed = [];
    for (const { region, w, h } of measured) {
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
      region.label.hidden = top === undefined;
      if (top === undefined) continue;
      region.label.style.left = `${center}px`;
      region.label.style.top = `${top}px`;
      placed.push({ left, right: left + w, top, bottom: top + h });
    }
  }

  function draw() {
    const { active, selected, view, overview } = navigation;
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
    placeLabels();
    const visibleBundles = bundlesFor(overview ? hierarchy.root : active?.module);
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
    for (const region of allRegions) {
      if (region.parent && (view.zoom <= 1.5 || (active !== region && active !== region.parent))) continue;
      if (view.zoom > 1.5 && region === active && region.children.length) continue;
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
          const point = byName.get(name);
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
        if (point.color !== color || (selected && point === selected)) continue;
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
      return;
    }
    const region = regionByModule.get(hierarchy.find(moduleName));
    if (region) openRegion(region);
  }

  function clearSelection() {
    detail.hidden = true;
    select.value = "";
    const region = navigation.active;
    preview.textContent = !region ? hint : region.children.length
      ? "Choose a submodule or select a declaration." : "Select a dot or choose a declaration.";
  }

  function openRegion(region) {
    if (!region.points.length) return;
    hovered = null;
    const previous = navigation.active;
    navigation.open(region, canAnimateCamera());
    updateRegion(previous);
    clearSelection();
    animateCamera();
    draw();
    canvas.focus?.({ preventScroll: true });
  }

  function relation(title, names) {
    const block = element("ul", "research-map-relations");
    const related = [...new Set(names ?? [])];
    const available = related.filter((name) => byName.has(name));
    const count = available.length === related.length ? String(related.length) : `${related.length} total, ${available.length} on map`;
    const summary = element("summary", "", `${title} (${count})`);
    const list = element("details", "research-map-relation");
    list.open = available.length > 0 && available.length <= 5;
    list.append(summary, block);
    for (const name of available) {
      const item = element("li", "");
      const link = button(name.split(".").at(-1), () => openPoint(byName.get(name), true), "research-map-related");
      link.title = name;
      link.setAttribute("aria-label", `Show ${name} on the map`);
      const namespace = element("small", "", name.split(".").slice(0, -1).join("."));
      if (namespace.textContent) link.append(namespace);
      item.append(link);
      block.append(item);
    }
    if (related.length && !available.length) list.append(element("p", "muted", "No related declarations match this map."));
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
    const statement = element("div", "math-presentation");
    renderStatement(statement, point.entry);
    detail.replaceChildren(head, statement,
      relation("Depends on", point.entry.dependencies),
      relation("Used by", point.entry.dependents));
    detail.hidden = false;
    draw();
    if (focusDetail) {
      title.focus?.({ preventScroll: true });
      title.scrollIntoView?.({ block: "start" });
    }
  }

  function zoomBy(factor, x, y) {
    const previous = navigation.active;
    if (!navigation.zoom(factor, x, y, canAnimateCamera())) return;
    hovered = null;
    updateRegion(previous);
    if (navigation.active !== previous) clearSelection();
    animateCamera();
    draw();
  }

  function coords(event) {
    const rect = canvas.getBoundingClientRect();
    return [(event.clientX - rect.left) * width / rect.width, (event.clientY - rect.top) * height / rect.height];
  }

  function hit(x, y) {
    let nearest = null;
    let best = 10;
    for (const point of points) {
      const [px, py] = pointOnScreen(point);
      const distance = Math.hypot(x - px, y - py);
      if (distance < best) { best = distance; nearest = point; }
    }
    return nearest;
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
    } else if (event.pointerType !== "touch" && cameraFrame === null) {
      const point = hit(x, y);
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
    if (!navigation.overview) {
      const child = navigation.active?.children.find((region) => {
        const [px, py] = screen(region.x, region.y);
        return Math.hypot(x - px, y - py) <= region.radius * navigation.view.zoom + 5;
      });
      if (child) { openRegion(child); return; }
      const point = hit(x, y);
      if (point) openPoint(point, true);
      return;
    }
    const region = regions.find((item) => {
      const [px, py] = screen(item.x, item.y);
      return Math.hypot(x - px, y - py) < item.radius + 14;
    });
    if (region) openRegion(region);
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
    } else if (event.key === "0" || event.key === "Escape") reset();
    else {
      const factor = zoomFactorForKey(event.key);
      if (!factor) return;
      zoomBy(factor);
    }
    event.preventDefault();
  });
  select.addEventListener("change", () => openPoint(byName.get(select.value), true));
  const zoomOut = button("−", () => zoomBy(1 / ZOOM_STEP), "map-zoom-button");
  zoomOut.setAttribute("aria-label", "Zoom out");
  const zoomIn = button("+", () => zoomBy(ZOOM_STEP), "map-zoom-button");
  zoomIn.setAttribute("aria-label", "Zoom in");
  controls.append(parentControl, zoomOut, zoomIn, button("Whole map", () => reset()));
  stage.append(canvas, ...allRegions.map((region) => region.label), hoverLabel);
  const emptyBundles = [];
  const overviewFooter = element("div", "research-map-overview");
  overviewFooter.append(...overviewHeader);
  section.append(header, controls, stage, controlsSlot, legend, preview, picker, detail, connectionDetails, overviewFooter);
  const sortedPoints = [...points].sort((a, b) => a.entry.name.localeCompare(b.entry.name));
  populatePicker(null);
  reset(false);
  if (selectedName) openPoint(byName.get(selectedName));
  // This section is returned before it is mounted, so measure again after attachment.
  if (typeof requestAnimationFrame === "function") requestAnimationFrame(draw);
  window.addEventListener?.("resize", onResize);
  return section;

  function onResize() {
    if (section.isConnected) draw();
    else window.removeEventListener("resize", onResize);
  }
}
