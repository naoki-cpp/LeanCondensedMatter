import { DEFINITION_KINDS } from "./declaration-model.js";

const size = 180;
const goldenAngle = Math.PI * (3 - Math.sqrt(5));
const categories = [
  ["Theorems", "#90bed2", (entry) => entry.kind === "theorem"],
  ["Definitions", "#8dceb1", (entry) => DEFINITION_KINDS.has(entry.kind)],
  ["Other declarations", "#dfbd86", () => true],
];

function clusterPoints(entries, largest) {
  return entries.map((entry, index) => {
    const distance = (size / 2 - 7) * Math.sqrt(index / largest);
    const angle = index * goldenAngle;
    return {
      entry,
      x: size / 2 + distance * Math.cos(angle),
      y: size / 2 + distance * Math.sin(angle),
      color: categories.find(([, , matches]) => matches(entry))[1],
    };
  });
}

function nearestPoint(canvas, points, event) {
  const bounds = canvas.getBoundingClientRect();
  const x = (event.clientX - bounds.left) * size / bounds.width;
  const y = (event.clientY - bounds.top) * size / bounds.height;
  let best = null;
  let limit = (6 * size / bounds.width) ** 2;
  for (const point of points) {
    const distance = (point.x - x) ** 2 + (point.y - y) ** 2;
    if (distance < limit) {
      best = point;
      limit = distance;
    }
  }
  return best;
}

function drawCluster(canvas, points, largest) {
  const scale = Math.max(2, window.devicePixelRatio || 1);
  canvas.width = size * scale;
  canvas.height = size * scale;
  const ctx = canvas.getContext("2d");
  if (!ctx) return;
  ctx.scale(scale, scale);
  const center = size / 2;
  const radius = center - 7;
  ctx.strokeStyle = "#42605a";
  ctx.beginPath();
  ctx.arc(center, center, radius * Math.sqrt(points.length / largest) + 4, 0, 2 * Math.PI);
  ctx.stroke();

  for (const [, color] of categories) {
    ctx.fillStyle = color;
    ctx.beginPath();
    for (const { x, y, color: pointColor } of points) {
      if (pointColor !== color) continue;
      ctx.moveTo(x + 1, y);
      ctx.arc(x, y, 1, 0, 2 * Math.PI);
    }
    ctx.fill();
  }
}

export function renderResearchMap(children, entriesFor, onOpenDeclaration) {
  const section = document.createElement("section");
  section.className = "research-map";
  section.setAttribute("aria-labelledby", "research-map-title");
  const heading = document.createElement("h3");
  heading.id = "research-map-title";
  heading.textContent = "Research map";
  section.append(heading);
  const legend = document.createElement("ul");
  legend.className = "research-map-legend";
  legend.setAttribute("aria-label", "One dot per non-generated declaration");
  for (const [label, color] of categories) {
    const item = document.createElement("li");
    const dot = document.createElement("i");
    dot.style.backgroundColor = color;
    dot.setAttribute("aria-hidden", "true");
    item.append(dot, document.createTextNode(label));
    legend.append(item);
  }
  section.append(legend);

  const grid = document.createElement("div");
  grid.className = "research-map-grid";
  const viewport = document.createElement("div");
  viewport.className = "research-map-viewport";
  viewport.append(grid);
  const controls = document.createElement("div");
  controls.className = "research-map-controls";
  controls.setAttribute("role", "group");
  controls.setAttribute("aria-label", "Research map zoom");
  let zoom = 1;
  for (const [text, label, step] of [["−", "Zoom out on map", -.5], ["+", "Zoom in on map", .5], ["Fit", "Show whole map", 0]]) {
    const control = document.createElement("button");
    control.type = "button";
    control.textContent = text;
    control.setAttribute("aria-label", label);
    control.addEventListener("click", () => {
      zoom = step ? Math.max(1, Math.min(3, zoom + step)) : 1;
      grid.style.width = `${zoom * 100}%`;
      grid.style.setProperty("--map-zoom", zoom);
      if (zoom === 1) viewport.scrollTo(0, 0);
    });
    controls.append(control);
  }
  const preview = document.createElement("p");
  preview.className = "research-map-preview";
  preview.setAttribute("aria-live", "off");
  const mapHint = "Select a dot to open its dependency graph.";
  preview.textContent = mapHint;
  const picker = document.createElement("label");
  picker.className = "research-map-picker";
  picker.hidden = true;
  const caption = document.createElement("span");
  const select = document.createElement("select");
  picker.append(caption, select);
  select.addEventListener("change", () => onOpenDeclaration(select.value));
  const largest = children.reduce((max, child) => Math.max(max, child.counts.total), 1);
  for (const child of children) {
    const entries = entriesFor(child);
    const points = clusterPoints(entries, largest);
    const button = document.createElement("button");
    button.type = "button";
    button.className = "research-map-region";
    button.setAttribute("aria-pressed", "false");
    button.disabled = child.counts.total === 0;
    button.addEventListener("click", (event) => {
      for (const region of grid.children) region.setAttribute("aria-pressed", String(region === button));
      caption.textContent = `Declaration in ${name.textContent}`;
      select.replaceChildren(...entries.map((entry) => {
        const option = document.createElement("option");
        option.value = entry.name;
        option.textContent = entry.name;
        return option;
      }));
      picker.hidden = false;
      const connections = (entry) => entry.dependencies.length + entry.dependents.length;
      const point = event?.target === canvas ? nearestPoint(canvas, points, event) : null;
      const initial = point?.entry ?? entries.reduce((best, entry) => connections(entry) > connections(best) ? entry : best);
      select.value = initial.name;
      onOpenDeclaration(initial.name);
    });
    const canvas = document.createElement("canvas");
    canvas.setAttribute("aria-hidden", "true");
    drawCluster(canvas, points, largest);
    canvas.addEventListener("pointermove", (event) => {
      preview.textContent = nearestPoint(canvas, points, event)?.entry.name ?? mapHint;
    });
    canvas.addEventListener("pointerleave", () => { preview.textContent = mapHint; });
    const name = document.createElement("strong");
    name.textContent = child.name.replace(/([a-z])([A-Z])/g, "$1 $2");
    const detail = document.createElement("small");
    const total = child.counts.total;
    detail.textContent = `${total.toLocaleString("en")} declaration${total === 1 ? "" : "s"}`;
    button.append(canvas, name, detail);
    grid.append(button);
  }
  section.append(controls, viewport, preview, picker);
  return section;
}
