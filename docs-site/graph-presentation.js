import { MAP_NODE_COLORS, ROOT_NODE_COLOR, ROOT_NODE_STROKE } from "./graph-style.js";

const colors = { theorem: "#4c7194", definition: "#a7cfbb", axiom: "#e5ca94", type: "#c9bbd9" };
const branches = ["#648875", "#7b9484", "#537968", "#8b9d8c"];

export function createGraphPresentation(mode) {
  const modules = mode === "modules";
  const node = (entry, { root = false, selected = false } = {}) => ({
    fill: modules ? (root ? MAP_NODE_COLORS.green : MAP_NODE_COLORS.blue) : root ? ROOT_NODE_COLOR
      : ["def", "abbrev", "opaque"].includes(entry.kind) ? colors.definition
      : entry.kind === "axiom" ? colors.axiom
      : ["inductive", "constructor", "recursor", "quotient"].includes(entry.kind) ? colors.type : colors.theorem,
    stroke: modules ? (selected || root ? "#edf5ee" : "#42605a")
      : selected ? "#173d2c" : root ? ROOT_NODE_STROKE : "#496553",
    "stroke-width": selected || root ? 2.4 : 1,
    "stroke-dasharray": entry.generated ? "2 2" : "none",
  });
  const edge = ({ tree = true, wrapper = false, typeOnly = false, branchIndex = 0, focused = false } = {}) => ({
    stroke: modules ? (tree ? MAP_NODE_COLORS.green : "#adc7bc") : tree ? branches[branchIndex % branches.length] : "#b9c9be",
    "stroke-width": !modules && wrapper ? 2 : tree ? 1.7 : 0.8,
    "stroke-opacity": tree ? 0.85 : focused ? 0.55 : 0.07,
    "stroke-dasharray": !modules && wrapper ? "7 5" : !modules && typeOnly ? "2 5" : tree ? "none" : "4 7",
    "marker-end": modules ? "url(#import-arrow)" : tree ? "url(#dependency-arrow)" : "url(#dependency-arrow-muted)",
  });
  return {
    node, edge,
    legend() {
      const items = [{ label: modules ? "module" : "theorem", shape: "node", attributes: node({ kind: "theorem" }) }];
      if (!modules) items.push(
        { label: "definition", shape: "node", attributes: node({ kind: "def" }) },
        { label: "axiom", shape: "node", attributes: node({ kind: "axiom" }) },
        { label: "type / constructor / recursor", shape: "node", attributes: node({ kind: "inductive" }) },
        { label: "type reference", shape: "edge", attributes: edge({ typeOnly: true }) });
      items.push({ label: modules ? "import" : "dependency", shape: "edge", attributes: edge() },
        { label: "cross-link", shape: "edge", attributes: edge({ tree: false }) });
      if (!modules) items.push({ label: "direct wrapper", shape: "edge", attributes: edge({ wrapper: true }) });
      return items;
    },
  };
}
