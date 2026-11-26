export const BRANCH_COLORS = [
  "#387663", "#4c7194", "#9a753c", "#7c648f", "#95636a", "#527d88",
  "#6d7c43", "#926e53", "#526d83", "#826877", "#5b8070", "#897a4c",
];

export const ROOT_NODE_COLOR = "#21664c";
export const ROOT_NODE_STROKE = "#d3e3d8";
export const ROOT_LABEL_COLOR = "#173d2c";

export function graphNodeRadius({ depth = 1, root = false, selected = false } = {}) {
  return root ? 12 : depth === 1 ? 6.5 : selected ? 6 : 4.2;
}

export function graphNodeLabelAttributes({ depth = 1, root = false } = {}) {
  return {
    fill: root ? ROOT_LABEL_COLOR : "#354b40",
    "font-family": "var(--code-font)",
    "font-size": root ? 13 : depth === 1 ? 12 : 11,
    "font-weight": root ? 600 : 400,
    "paint-order": "stroke",
    stroke: "#f5f7f3",
    "stroke-width": root ? 4 : 3,
    "stroke-linejoin": "round",
    "dominant-baseline": "middle",
  };
}

export function graphLabelLines(name, limit = 26) {
  const characters = Array.from(name);
  if (characters.length <= limit) return [name];
  const separator = characters.slice(0, limit).findLastIndex((character) => character === "_" || character === ".");
  const cut = separator >= limit / 2 && characters.length - separator - 1 <= limit ? separator + 1 : limit;
  const remainder = characters.slice(cut);
  return [characters.slice(0, cut).join(""), remainder.length <= limit ? remainder.join("") : remainder.slice(0, limit - 1).join("") + "…"];
}
