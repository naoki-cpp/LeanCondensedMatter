export const ROOT_NODE_COLOR = "#21664c";
export const ROOT_NODE_STROKE = "#d3e3d8";
export const ROOT_LABEL_COLOR = "#173d2c";
export const MAP_NODE_COLORS = { blue: "#90bed2", green: "#8dceb1" };

export function graphNodeRadius({ depth = 1, root = false, selected = false } = {}) {
  return root ? 12 : depth === 1 ? 6.5 : selected ? 6 : 4.2;
}

export function graphNodeLabelAttributes({ depth = 1, root = false, selected = false } = {}) {
  return {
    fill: root ? `var(--graph-root-label, ${ROOT_LABEL_COLOR})` : "var(--graph-label, #213e30)",
    "font-family": "var(--ui-font)",
    "font-size": root ? 16 : depth === 1 ? 14 : 13,
    "font-weight": root || selected ? 600 : 400,
    "paint-order": "stroke",
    stroke: "var(--graph-bg, #f7f9f6)",
    "stroke-width": root ? 4 : 3,
    "stroke-linejoin": "round",
    "dominant-baseline": "middle",
  };
}

export function graphLabelLines(name, limit = 26) {
  const characters = Array.from(name);
  if (characters.length <= limit) return [name];
  const breaks = characters.flatMap((character, index) =>
    character === "_" || character === "." || (index > 0 && /[a-z]/.test(characters[index - 1]) && /[A-Z]/.test(character))
      ? [character === "_" || character === "." ? index + 1 : index] : []);
  const candidates = breaks.filter((cut) => cut <= limit && characters.length - cut <= limit);
  const cut = candidates.sort((a, b) => Math.abs(a - characters.length / 2) - Math.abs(b - characters.length / 2))[0] ?? limit;
  const remainder = characters.slice(cut);
  return [characters.slice(0, cut).join(""), remainder.length <= limit ? remainder.join("") : remainder.slice(0, limit - 1).join("") + "…"];
}
