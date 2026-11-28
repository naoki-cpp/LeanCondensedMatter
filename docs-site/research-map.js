import { DEFINITION_KINDS } from "./declaration-model.js";
import { renderStatement } from "./statement-view.js";

const width = 960;
const height = 670;
const goldenAngle = Math.PI * (3 - Math.sqrt(5));
const categories = [
  ["Theorems", "#90bed2", (entry) => entry.kind === "theorem"],
  ["Definitions", "#8dceb1", (entry) => DEFINITION_KINDS.has(entry.kind)],
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

export function renderResearchMap(children, entriesFor, onOpenDeclaration, onRegionChange, overviewHeader) {
  const section = element("section", "research-map");
  const heading = element("h3", "", "Declaration dependency map");
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
  const controls = element("div", "research-map-controls");
  const stage = element("div", "research-map-stage");
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
  picker.hidden = true;
  const caption = element("span", "", "Declaration");
  const select = element("select", "");
  picker.append(caption, select);
  const byName = new Map();
  const largest = Math.max(1, ...children.map((child) => child.counts.total));
  const columns = Math.min(3, Math.max(1, children.length));
  const rows = Math.max(1, Math.ceil(children.length / columns));
  const spacing = Math.min(91, (height / rows - 46) / 2);
  const allRegions = [];
  const shortModule = (name) => name.replace(/^LeanCondensedMatter\./, "");
  function placeCloud(points, scope, x, y, radius) {
    points.forEach((point, i) => {
      const distance = radius * .94 * Math.sqrt(i / points.length);
      const angle = goldenAngle * i;
      point.positions.set(scope, { x: x + distance * Math.cos(angle), y: y + distance * Math.sin(angle) });
    });
  }
  function buildRegion(moduleName, x, y, radius, entries, parent = null) {
    const name = moduleName.split(".").at(-1).replace(/([a-z])([A-Z])/g, "$1 $2");
    const region = { name, moduleName, x, y, radius, parent, children: [] };
    allRegions.push(region);
    const prefix = moduleName + ".";
    const groups = new Map();
    for (const entry of entries) {
      const path = shortModule(entry.module);
      const key = path.startsWith(prefix) ? path.slice(prefix.length).split(".")[0] : "";
      if (!groups.has(key)) groups.set(key, []);
      groups.get(key).push(entry);
    }
    const ordered = [...groups].sort(([a], [b]) => a.localeCompare(b));
    const cellColumns = Math.max(1, Math.ceil(Math.sqrt(ordered.length)));
    const cellRows = Math.ceil(ordered.length / cellColumns);
    const cell = region.radius * Math.SQRT2 / Math.max(cellColumns, cellRows);
    region.points = ordered.flatMap(([key, records], i) => {
      const grouped = ordered.length > 1;
      const gx = grouped ? x + ((i % cellColumns) - (cellColumns - 1) / 2) * cell : x;
      const gy = grouped ? y + (Math.floor(i / cellColumns) - (cellRows - 1) / 2) * cell : y;
      const groupRadius = grouped ? cell * .34 : region.radius * .75;
      let points;
      if (key) {
        const child = buildRegion(prefix + key, gx, gy, groupRadius, records, region);
        region.children.push(child);
        points = child.points;
      } else {
        points = records.map((entry) => {
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
    const radius = spacing * Math.sqrt(child.counts.total / largest);
    const region = buildRegion(shortModule(child.fullName), x, y, radius, entriesFor(child));
    for (const point of region.points) point.topRegion = region;
    placeCloud(region.points, null, x, y, radius);
    return region;
  });

  function makeLabel(region) {
    const { name } = region;
    const label = button(name, () => openRegion(region), "research-map-region");
    label.disabled = region.points.length === 0;
    label.setAttribute("aria-label", `${name}, ${region.points.length} declarations`);
    label.append(element("small", "", `${region.points.length.toLocaleString("en")} declaration${region.points.length === 1 ? "" : "s"}`));
    return label;
  }
  const points = [...byName.values()];
  function collectBundles(clusters, records, clusterOf) {
    const order = new Map(clusters.map((region, index) => [region, index]));
    const connections = new Map();
    for (const point of records) {
      const source = order.get(clusterOf(point));
      if (source === undefined) continue;
      for (const name of new Set(point.entry.dependencies ?? [])) {
        const targetPoint = byName.get(name);
        const target = targetPoint && order.get(clusterOf(targetPoint));
        if (target === undefined || target === source) continue;
        const a = Math.min(source, target);
        const b = Math.max(source, target);
        const key = `${a}:${b}`;
        if (!connections.has(key)) connections.set(key, { a: clusters[a], b: clusters[b], ab: 0, ba: 0 });
        const connection = connections.get(key);
        if (source === a) connection.ab += 1;
        else connection.ba += 1;
      }
    }
    return [...connections.values()].sort((a, b) => b.ab + b.ba - a.ab - a.ba);
  }
  const bundles = collectBundles(regions, points, (point) => point.topRegion);
  const submoduleBundles = new Map();
  function bundlesFor(region) {
    if (!region?.children.length) return emptyBundles;
    if (!submoduleBundles.has(region)) {
      const childOf = new Map(region.children.flatMap((child) => child.points.map((point) => [point, child])));
      submoduleBundles.set(region, collectBundles(region.children, region.points, (point) => childOf.get(point)));
    }
    return submoduleBundles.get(region);
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
  let view = { x: width / 2, y: height / 2, zoom: 1 };
  let active = null;
  const parentControl = button("Parent region", () => { if (active?.parent) openRegion(active.parent); });
  parentControl.hidden = true;
  let selected = null;
  let drag = null;
  let cameraFrame = null;
  let zoomingToParent = false;
  let previousScope = null;
  let layoutBlend = 1;
  const screen = (x, y) => [(x - view.x) * view.zoom + width / 2, (y - view.y) * view.zoom + height / 2];
  function positionInScope(point, scope) {
    for (let candidate = scope; candidate; candidate = candidate.parent) {
      const position = point.positions.get(candidate);
      if (position) return position;
    }
    return point.positions.get(null);
  }
  function pointOnScreen(point) {
    const scope = view.zoom > 1.5 || cameraFrame !== null ? active : null;
    const from = positionInScope(point, previousScope);
    const to = positionInScope(point, scope);
    return screen(from.x + (to.x - from.x) * layoutBlend, from.y + (to.y - from.y) * layoutBlend);
  }

  function stopCamera() {
    if (cameraFrame !== null) cancelAnimationFrame(cameraFrame);
    cameraFrame = null;
    zoomingToParent = false;
    layoutBlend = 1;
  }

  function glideTo(target) {
    stopCamera();
    if (window.matchMedia?.("(prefers-reduced-motion: reduce)").matches ||
        typeof requestAnimationFrame !== "function") {
      view = target;
      draw();
      return;
    }
    const start = { ...view };
    let startedAt;
    function step(now) {
      startedAt ??= now;
      const progress = Math.min(1, (now - startedAt) / 420);
      const eased = progress * progress * (3 - 2 * progress);
      layoutBlend = eased;
      view = {
        x: start.x + (target.x - start.x) * eased,
        y: start.y + (target.y - start.y) * eased,
        zoom: start.zoom * (target.zoom / start.zoom) ** eased,
      };
      draw();
      cameraFrame = progress < 1 && section.isConnected ? requestAnimationFrame(step) : null;
    }
    cameraFrame = requestAnimationFrame(step);
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
    const visible = [];
    for (const region of allRegions) {
      const focused = view.zoom > 1.5 && region === active;
      region.label.hidden = view.zoom > 1.5 && active
        ? !focused && region.parent !== active
        : Boolean(region.parent);
      if (!region.label.hidden) visible.push({ region, focused });
    }
    const stageWidth = stage.clientWidth;
    const stageHeight = stage.clientHeight;
    const measured = visible.map(({ region, focused }) => ({
      region, focused, w: region.label.offsetWidth, h: region.label.offsetHeight,
    })).sort((a, b) => Number(b.focused) - Number(a.focused));
    const placed = [];
    for (const { region, focused, w, h } of measured) {
      const [x, y] = screen(region.x, region.y + region.radius);
      if (!stageWidth || !stageHeight) continue;
      const pinned = focused && region.children.length > 0;
      const anchorX = pinned ? stageWidth / 2 : x / width * stageWidth;
      const anchorY = y / height * stageHeight;
      const [, above] = screen(region.x, region.y - region.radius);
      const candidates = pinned ? [4] : [anchorY + 6, above / height * stageHeight - h - 6, anchorY + h + 10];
      const center = Math.max(w / 2 + 4, Math.min(stageWidth - w / 2 - 4, anchorX));
      const left = center - w / 2;
      const top = candidates.map((value) => Math.max(4, Math.min(stageHeight - h - 4, value)))
        .find((value) => placed.every((box) => left >= box.right + 4 || left + w + 4 <= box.left ||
          value >= box.bottom + 4 || value + h + 4 <= box.top));
      region.label.hidden = !focused && top === undefined;
      if (top === undefined) continue;
      region.label.style.left = `${center}px`;
      region.label.style.top = `${top}px`;
      placed.push({ left, right: left + w, top, bottom: top + h });
    }
  }

  function draw() {
    canvas.style.touchAction = view.zoom > 1.5 ? "none" : "pan-y";
    placeLabels();
    const overview = view.zoom <= 1.5;
    const visibleBundles = overview ? bundles : bundlesFor(active);
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
  }

  function setRegion(region) {
    if (active === region) return;
    previousScope = active;
    active = region;
    onRegionChange(region?.moduleName ?? null, browseMap);
    parentControl.hidden = !region?.parent;
    picker.hidden = !region;
    if (!region) return;
    caption.textContent = `Declaration in ${region.name}`;
    const placeholder = element("option", "", "Choose a declaration");
    placeholder.value = "";
    placeholder.disabled = true;
    select.replaceChildren(placeholder, ...region.points.map(({ entry }) => {
      const option = element("option", "", entry.name);
      option.value = entry.name;
      return option;
    }));
    select.value = "";
  }

  function reset() {
    stopCamera();
    view = { x: width / 2, y: height / 2, zoom: 1 };
    selected = null;
    detail.hidden = true;
    setRegion(null);
    preview.textContent = hint;
    draw();
  }

  function browseMap(moduleName) {
    if (moduleName === "LeanCondensedMatter") {
      reset();
      return;
    }
    const region = allRegions.find((item) => item.moduleName === moduleName);
    if (region) openRegion(region);
  }

  function regionView(region) {
    if (region.children.length) {
      const extents = [...region.children, ...region.points.filter((point) => point.region === region)];
      const left = Math.min(...extents.map(({ x, radius = 0 }) => x - radius));
      const right = Math.max(...extents.map(({ x, radius = 0 }) => x + radius));
      const top = Math.min(...extents.map(({ y, radius = 0 }) => y - radius));
      const bottom = Math.max(...extents.map(({ y, radius = 0 }) => y + radius));
      // Leave room for the parent title at the top and the child labels at the bottom.
      const zoom = Math.min((width - 104) / (right - left), (height - 140) / (bottom - top));
      return { x: (left + right) / 2, y: (top + bottom) / 2, zoom };
    }
    return { x: region.x, y: region.y, zoom: height / (3 * region.radius) };
  }

  function openRegion(region, { focus = true } = {}) {
    if (!region.points.length) return;
    setRegion(region);
    selected = null;
    detail.hidden = true;
    select.value = "";
    preview.textContent = region.children.length ? "Choose a submodule or select a declaration." : "Select a dot or choose a declaration.";
    glideTo(regionView(region));
    if (focus) canvas.focus?.({ preventScroll: true });
  }

  function relation(title, names) {
    const block = element("div", "research-map-relations");
    const available = (names ?? []).filter((name) => byName.has(name));
    const summary = element("summary", "", `${title} (${available.length})`);
    const list = element("details", "");
    list.open = available.length > 0 && available.length <= 12;
    list.append(summary, block);
    for (const name of available) {
      block.append(button(name.split(".").at(-1), (event) => {
        openPoint(byName.get(name));
        if (event?.detail === 0) detail.querySelector("h4")?.focus();
      }));
    }
    return list;
  }

  function openPoint(point) {
    if (!point) return;
    stopCamera();
    setRegion(point.region);
    selected = point;
    select.value = point.entry.name;
    view = { x: point.x, y: point.y, zoom: Math.max(height / (3 * point.region.radius), view.zoom) };
    const title = element("h4", "", point.entry.name);
    title.tabIndex = -1;
    const statement = element("div", "math-presentation");
    renderStatement(statement, point.entry);
    detail.replaceChildren(title, statement,
      relation("Depends on", point.entry.dependencies),
      relation("Used by", point.entry.dependents),
      button("Open full dependency graph", () => onOpenDeclaration(point.entry.name)));
    detail.hidden = false;
    draw();
  }

  function zoomBy(factor, x = width / 2, y = height / 2) {
    if (factor < 1 && zoomingToParent && cameraFrame !== null) return;
    stopCamera();
    const limit = Math.max(24, active ? height / active.radius : 24, view.zoom);
    const next = Math.max(1, Math.min(limit, view.zoom * factor));
    if (factor < 1 && active) {
      const parent = active.parent;
      if (parent) {
        const threshold = Math.max(regionView(parent).zoom, regionView(active).zoom / 1.5);
        if (next <= threshold * (1 + Number.EPSILON)) {
          openRegion(parent, { focus: false });
          zoomingToParent = true;
          return;
        }
      } else if (next <= 1.5) {
        reset();
        return;
      }
    }
    view.x += (x - width / 2) * (1 / view.zoom - 1 / next);
    view.y += (y - height / 2) * (1 / view.zoom - 1 / next);
    view.zoom = next;
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
    if (!event.isPrimary || event.button !== 0 || (event.pointerType === "touch" && view.zoom <= 1.5)) return;
    stopCamera();
    drag = { id: event.pointerId, start: coords(event), view: { ...view }, moved: false };
    canvas.setPointerCapture(event.pointerId);
  });
  canvas.addEventListener("pointermove", (event) => {
    const [x, y] = coords(event);
    if (drag?.id === event.pointerId) {
      const dx = x - drag.start[0];
      const dy = y - drag.start[1];
      if (!drag.moved && Math.hypot(dx, dy) < 7) return;
      drag.moved = true;
      view.x = drag.view.x - dx / view.zoom;
      view.y = drag.view.y - dy / view.zoom;
      draw();
    } else if (view.zoom > 1.5) {
      const name = hit(x, y)?.entry.name ?? "Select a dot or choose a declaration.";
      if (preview.textContent !== name) preview.textContent = name;
    }
  });
  canvas.addEventListener("pointercancel", (event) => {
    if (drag?.id === event.pointerId) drag = null;
  });
  canvas.addEventListener("click", (event) => {
    if (drag?.moved) { drag = null; return; }
    drag = null;
    const [x, y] = coords(event);
    if (view.zoom > 1.5) {
      const child = active?.children.find((region) => {
        const [px, py] = screen(region.x, region.y);
        return Math.hypot(x - px, y - py) <= region.radius * view.zoom + 5;
      });
      if (child) { openRegion(child); return; }
      const point = hit(x, y);
      if (point) openPoint(point);
      return;
    }
    const region = regions.find((item) => {
      const [px, py] = screen(item.x, item.y);
      return Math.hypot(x - px, y - py) < item.radius + 14;
    });
    if (region) openRegion(region);
  });
  canvas.addEventListener("wheel", (event) => {
    if (!event.ctrlKey && !event.metaKey) return;
    event.preventDefault();
    zoomBy(Math.exp(-Math.max(-80, Math.min(80, event.deltaY)) * .008), ...coords(event));
  }, { passive: false });
  canvas.addEventListener("keydown", (event) => {
    const shift = { ArrowLeft: [-1, 0], ArrowRight: [1, 0], ArrowUp: [0, -1], ArrowDown: [0, 1] }[event.key];
    if (shift) {
      stopCamera();
      view.x += shift[0] * 70 / view.zoom;
      view.y += shift[1] * 70 / view.zoom;
      draw();
    } else if (event.key === "+" || event.key === "=") zoomBy(1.5);
    else if (event.key === "-") zoomBy(1 / 1.5);
    else if (event.key === "0" || event.key === "Escape") reset();
    else return;
    event.preventDefault();
  });
  select.addEventListener("change", () => openPoint(byName.get(select.value)));
  controls.append(parentControl, button("Zoom out", () => zoomBy(1 / 1.5)), button("Zoom in", () => zoomBy(1.5)), button("Whole map", reset));
  stage.append(canvas, ...allRegions.map((region) => region.label));
  const emptyBundles = [];
  const overviewFooter = element("div", "research-map-overview");
  overviewFooter.append(...overviewHeader);
  section.append(heading, legend, controls, stage, preview, picker, detail, connectionDetails, overviewFooter);
  reset();
  // This section is returned before it is mounted, so measure again after attachment.
  if (typeof requestAnimationFrame === "function") requestAnimationFrame(draw);
  window.addEventListener?.("resize", onResize);
  return section;

  function onResize() {
    if (section.isConnected) draw();
    else window.removeEventListener("resize", onResize);
  }
}
