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

export function renderResearchMap(children, entriesFor, onOpenDeclaration) {
  const section = element("section", "research-map");
  const heading = element("h3", "", "Research map");
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
  const hint = "Choose a region to zoom in, then select a dot.";
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
  const regions = children.map((child, index) => {
    const name = child.name.replace(/([a-z])([A-Z])/g, "$1 $2");
    const x = ((index % columns) + 0.5) * width / columns + (Math.floor(index / columns) % 2 ? 20 : -20);
    const y = (Math.floor(index / columns) + 0.44) * height / rows;
    const region = { name, x, y, radius: spacing * Math.sqrt(child.counts.total / largest) };
    region.points = entriesFor(child).map((entry, i) => {
      const distance = spacing * Math.sqrt(i / largest);
      const angle = goldenAngle * i;
      const point = { entry, region, x: x + distance * Math.cos(angle), y: y + distance * Math.sin(angle),
        color: categories.find(([, , matches]) => matches(entry))[1] };
      byName.set(entry.name, point);
      return point;
    });
    const label = button(name, () => openRegion(region), "research-map-region");
    label.disabled = region.points.length === 0;
    label.setAttribute("aria-label", `${name}, ${region.points.length} declarations`);
    label.append(element("small", "", `${region.points.length.toLocaleString("en")} declaration${region.points.length === 1 ? "" : "s"}`));
    region.label = label;
    return region;
  });
  const points = [...byName.values()];
  const regionOrder = new Map(regions.map((region, index) => [region, index]));
  const connections = new Map();
  for (const point of points) {
    const source = regionOrder.get(point.region);
    for (const name of new Set(point.entry.dependencies ?? [])) {
      const targetPoint = byName.get(name);
      if (!targetPoint || targetPoint.region === point.region) continue;
      const target = regionOrder.get(targetPoint.region);
      const a = Math.min(source, target);
      const b = Math.max(source, target);
      const key = `${a}:${b}`;
      if (!connections.has(key)) connections.set(key, { a: regions[a], b: regions[b], ab: 0, ba: 0 });
      const connection = connections.get(key);
      if (source === a) connection.ab += 1;
      else connection.ba += 1;
    }
  }
  const bundles = [...connections.values()].sort((a, b) => b.ab + b.ba - a.ab - a.ba);
  const connectionDetails = element("details", "research-map-connections");
  if (bundles.length) {
    const list = element("ul", "");
    for (const { a, b, ab, ba } of bundles) {
      const directions = [];
      if (ab) directions.push(`${a.name} → ${b.name}: ${ab.toLocaleString("en")}`);
      if (ba) directions.push(`${b.name} → ${a.name}: ${ba.toLocaleString("en")}`);
      list.append(element("li", "", directions.join(" · ")));
    }
    connectionDetails.append(element("summary", "", "Dependencies between regions"), list);
  }
  let view = { x: width / 2, y: height / 2, zoom: 1 };
  let active = null;
  let selected = null;
  let drag = null;
  let cameraFrame = null;
  const screen = (x, y) => [(x - view.x) * view.zoom + width / 2, (y - view.y) * view.zoom + height / 2];

  function stopCamera() {
    if (cameraFrame !== null) cancelAnimationFrame(cameraFrame);
    cameraFrame = null;
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
    const [x, y] = screen(from.x, from.y);
    const [tx, ty] = screen(to.x, to.y);
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

  function draw() {
    canvas.style.touchAction = view.zoom > 1.5 ? "none" : "pan-y";
    for (const region of regions) {
      const focused = view.zoom > 1.5 && region === active;
      region.label.hidden = view.zoom > 1.5 && !focused;
      const [x, y] = screen(region.x, region.y + region.radius + 11);
      region.label.style.left = `${focused ? Math.max(16, Math.min(84, x / width * 100)) : x / width * 100}%`;
      region.label.style.top = `${focused ? Math.max(4, Math.min(82, y / height * 100)) : y / height * 100}%`;
    }
    if (!ctx) return;
    ctx.setTransform(2, 0, 0, 2, 0, 0);
    ctx.clearRect(0, 0, width, height);
    if (view.zoom <= 1.5) {
      ctx.strokeStyle = "rgba(170, 199, 188, .33)";
      ctx.lineCap = "round";
      for (const { a, b, ab, ba } of bundles) {
        const angle = Math.atan2(b.y - a.y, b.x - a.x);
        const dx = Math.cos(angle);
        const dy = Math.sin(angle);
        ctx.lineWidth = 1 + Math.log10(ab + ba + 1) * 2;
        ctx.beginPath();
        ctx.moveTo(...screen(a.x + dx * (a.radius + 6), a.y + dy * (a.radius + 6)));
        ctx.lineTo(...screen(b.x - dx * (b.radius + 6), b.y - dy * (b.radius + 6)));
        ctx.stroke();
      }
      ctx.lineCap = "butt";
      ctx.lineWidth = 1;
    }
    for (const region of regions) {
      ctx.strokeStyle = "#42605a";
      ctx.beginPath();
      ctx.arc(...screen(region.x, region.y), (region.radius + 5) * view.zoom, 0, 2 * Math.PI);
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
        const [x, y] = screen(point.x, point.y);
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
      ctx.arc(...screen(selected.x, selected.y), 5, 0, 2 * Math.PI);
      ctx.fill();
    }
  }

  function setRegion(region) {
    if (active === region) return;
    active = region;
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

  function openRegion(region) {
    if (!region.points.length) return;
    setRegion(region);
    selected = null;
    detail.hidden = true;
    select.value = "";
    preview.textContent = "Select a dot or choose a declaration.";
    glideTo({ x: region.x, y: region.y, zoom: Math.min(12, height / (3 * (region.radius + 5))) });
    canvas.focus?.({ preventScroll: true });
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
    view = { x: point.x, y: point.y, zoom: Math.max(5, view.zoom) };
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
    stopCamera();
    const next = Math.max(1, Math.min(24, view.zoom * factor));
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
      const [px, py] = screen(point.x, point.y);
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
  controls.append(button("Zoom out", () => zoomBy(1 / 1.5)), button("Zoom in", () => zoomBy(1.5)), button("Whole map", reset));
  stage.append(canvas, ...regions.map((region) => region.label));
  section.append(heading, legend, controls, stage, preview, picker, detail);
  if (bundles.length) section.append(connectionDetails);
  reset();
  return section;
}
