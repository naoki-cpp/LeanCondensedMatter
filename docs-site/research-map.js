const size = 128;
const goldenAngle = Math.PI * (3 - Math.sqrt(5));
const categories = [
  ["Theorems", "#90bed2", (counts) => counts.theorems],
  ["Definitions", "#8dceb1", (counts) => counts.definitions],
  ["Other declarations", "#dfbd86", (counts) => counts.total - counts.theorems - counts.definitions],
];

function drawCluster(canvas, counts, largest) {
  const scale = Math.min(2, window.devicePixelRatio || 1);
  canvas.width = size * scale;
  canvas.height = size * scale;
  const ctx = canvas.getContext("2d");
  if (!ctx) return;
  ctx.scale(scale, scale);
  const center = size / 2;
  const radius = center - 7;
  ctx.strokeStyle = "#42605a";
  ctx.beginPath();
  ctx.arc(center, center, radius * Math.sqrt(counts.total / largest) + 4, 0, 2 * Math.PI);
  ctx.stroke();

  let index = 0;
  for (const [, color, count] of categories) {
    ctx.fillStyle = color;
    ctx.beginPath();
    const end = index + count(counts);
    for (; index < end; index += 1) {
      const distance = radius * Math.sqrt(index / largest);
      const angle = index * goldenAngle;
      const x = center + distance * Math.cos(angle);
      const y = center + distance * Math.sin(angle);
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
  const picker = document.createElement("label");
  picker.className = "research-map-picker";
  picker.hidden = true;
  const caption = document.createElement("span");
  const select = document.createElement("select");
  picker.append(caption, select);
  select.addEventListener("change", () => onOpenDeclaration(select.value));
  const largest = children.reduce((max, child) => Math.max(max, child.counts.total), 1);
  for (const child of children) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "research-map-region";
    button.setAttribute("aria-pressed", "false");
    button.disabled = child.counts.total === 0;
    button.addEventListener("click", () => {
      for (const region of grid.children) region.setAttribute("aria-pressed", String(region === button));
      const entries = entriesFor(child);
      caption.textContent = `Declaration in ${name.textContent}`;
      select.replaceChildren(...entries.map((entry) => {
        const option = document.createElement("option");
        option.value = entry.name;
        option.textContent = entry.name;
        return option;
      }));
      picker.hidden = false;
      const connections = (entry) => entry.dependencies.length + entry.dependents.length;
      const initial = entries.reduce((best, entry) => connections(entry) > connections(best) ? entry : best);
      select.value = initial.name;
      onOpenDeclaration(initial.name);
    });
    const canvas = document.createElement("canvas");
    canvas.setAttribute("aria-hidden", "true");
    drawCluster(canvas, child.counts, largest);
    const name = document.createElement("strong");
    name.textContent = child.name.replace(/([a-z])([A-Z])/g, "$1 $2");
    const detail = document.createElement("small");
    const total = child.counts.total;
    detail.textContent = `${total.toLocaleString("en")} declaration${total === 1 ? "" : "s"}`;
    button.append(canvas, name, detail);
    grid.append(button);
  }
  section.append(grid, picker);
  return section;
}
