import { buildStatementModel } from "./statement-model.js";
import { renderLeanMath, renderTexMath } from "./lean-math.js";

function element(tag, text, className = "") {
  const result = document.createElement(tag);
  result.textContent = text;
  result.className = className;
  return result;
}

function leanDetails(title, text) {
  const details = element("details", "", "lean-source");
  details.append(element("summary", title), element("pre", text));
  return details;
}

export function renderStatement(container, entry) {
  const model = buildStatementModel(entry.structuredStatement);
  if (!model) {
    renderLeanMath(container, entry.statement);
    return;
  }
  function section(title) {
    container.append(element("h4", title));
  }
  function row(item, { named = true, includeSource = false } = {}) {
    const wrapper = element("div", "", "statement-row");
    if (named) wrapper.append(element("code", item.name + " :", "statement-variable"));
    const formula = element("div", "", "statement-expression");
    renderTexMath(formula, item.tex, item.typeText ?? item.text ?? "", { includeSource });
    wrapper.append(formula);
    container.append(wrapper);
  }
  if (model.settings.length) {
    section("Setting");
    for (const setting of model.settings) {
      container.append(element("p", setting.name + ": " + setting.text, "statement-setting"));
      container.append(leanDetails("Underlying typeclass assumptions", setting.evidence.map((binder) => binder.typeText).join("\n")));
    }
  }
  if (model.variables.length) {
    section("Variables");
    for (const variable of model.variables) row(variable);
  }
  if (model.assumptions.length) {
    section("Assumptions");
    for (const assumption of model.assumptions) row(assumption, { named: assumption.role !== "instance" });
  }
  section(entry.kind === "theorem" || entry.kind === "axiom" ? "Conclusion" : "Result type");
  row(model.conclusion, { named: false });
  if (model.fields.length) {
    section("Structure fields");
    container.append(element("p", "Field types are shown for a value named self.", "math-fallback-note"));
    for (const field of model.fields) row(field, { includeSource: true });
  }
  if (model.symbols.length) {
    const key = element("details", "", "lean-source");
    key.append(element("summary", "Symbol names"));
    const list = element("dl", "", "statement-symbols");
    for (const [full, short] of model.symbols) {
      list.append(element("dt", short), element("dd", full));
    }
    key.append(list);
    container.append(key);
  }
  container.append(leanDetails("Original Lean statement", entry.statement));
}
