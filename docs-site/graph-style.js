export const BRANCH_COLORS = [
  "#ff5f6d", "#ff9f43", "#2ed573", "#3b82f6", "#8b5cf6", "#ec4899",
  "#06b6d4", "#84cc16", "#f97316", "#a855f7", "#14b8a6", "#eab308",
];

export const ROOT_NODE_COLOR = "#71e7dc";
export const ROOT_NODE_STROKE = "#d9fffb";
export const ROOT_LABEL_COLOR = "#f5f7ff";

export function graphNodeRadius({ depth = 1, root = false, selected = false } = {}) {
  return root ? 12 : depth === 1 ? 6.5 : selected ? 6 : 4.2;
}

export function graphNodeLabelAttributes({ depth = 1, root = false, color = "#91a9ff" } = {}) {
  return {
    fill: root ? ROOT_LABEL_COLOR : color,
    "font-size": root ? 12.5 : depth === 1 ? 11.5 : 9,
    "font-weight": root || depth === 1 ? 750 : 600,
    "paint-order": "stroke",
    stroke: "#080c18",
    "stroke-width": root ? 4 : 3,
    "stroke-linejoin": "round",
    "pointer-events": "none",
    "dominant-baseline": "middle",
  };
}
