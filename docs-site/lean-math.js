const OPERATOR_MAP = new Map([
  ["∀", "\\forall"],
  ["∃!", "\\exists!"],
  ["∃", "\\exists"],
  ["→", "\\to"],
  ["↔", "\\leftrightarrow"],
  ["⟷", "\\longleftrightarrow"],
  ["⟹", "\\Longrightarrow"],
  ["⟺", "\\Longleftrightarrow"],
  ["↦", "\\mapsto"],
  ["⟶", "\\longrightarrow"],
  ["∧", "\\land"],
  ["∨", "\\lor"],
  ["¬", "\\lnot"],
  ["⊤", "\\top"],
  ["⊥", "\\bot"],
  ["=", "="],
  ["==", "="],
  ["!=", "\\ne"],
  ["≠", "\\ne"],
  ["<", "<"],
  [">", ">"],
  ["≤", "\\le"],
  ["≥", "\\ge"],
  ["<=", "\\le"],
  [">=", "\\ge"],
  ["∈", "\\in"],
  ["∉", "\\notin"],
  ["∋", "\\ni"],
  ["∌", "\\notni"],
  ["∣", "\\mid"],
  ["∥", "\\parallel"],
  ["∩", "\\cap"],
  ["∪", "\\cup"],
  ["⊆", "\\subseteq"],
  ["⊂", "\\subset"],
  ["⊇", "\\supseteq"],
  ["⊃", "\\supset"],
  ["⊓", "\\sqcap"],
  ["⊔", "\\sqcup"],
  ["⊕", "\\oplus"],
  ["⊗", "\\otimes"],
  ["×", "\\times"],
  ["∘", "\\circ"],
  ["⋅", "\\cdot"],
  ["·", "\\cdot"],
  ["+", "+"],
  ["-", "-"],
  ["*", "\\cdot"],
  ["/", "/"],
  [":=", "\\mathrel{:=}"],
  ["->", "\\to"],
  ["<->", "\\leftrightarrow"],
  ["=>", "\\mapsto"],
  ["∑", "\\sum"],
  ["∏", "\\prod"],
  ["∫", "\\int"],
  ["∞", "\\infty"],
  ["∂", "\\partial"],
  ["∇", "\\nabla"],
  ["∅", "\\varnothing"],
  ["≈", "\\approx"],
  ["≃", "\\simeq"],
  ["≅", "\\cong"],
  ["≡", "\\equiv"],
  ["∼", "\\sim"],
  ["∝", "\\propto"],
  ["ℕ", "\\mathbb{N}"],
  ["ℤ", "\\mathbb{Z}"],
  ["ℚ", "\\mathbb{Q}"],
  ["ℝ", "\\mathbb{R}"],
  ["ℂ", "\\mathbb{C}"],
]);

const GREEK_MAP = new Map([
  ["α", "\\alpha"], ["β", "\\beta"], ["γ", "\\gamma"], ["δ", "\\delta"],
  ["ε", "\\varepsilon"], ["ϵ", "\\epsilon"], ["ζ", "\\zeta"], ["η", "\\eta"],
  ["θ", "\\theta"], ["ϑ", "\\vartheta"], ["ι", "\\iota"], ["κ", "\\kappa"],
  ["λ", "\\lambda"], ["μ", "\\mu"], ["ν", "\\nu"], ["ξ", "\\xi"],
  ["π", "\\pi"], ["ϖ", "\\varpi"], ["ρ", "\\rho"], ["σ", "\\sigma"],
  ["ς", "\\varsigma"], ["τ", "\\tau"], ["υ", "\\upsilon"], ["φ", "\\varphi"],
  ["ϕ", "\\phi"], ["χ", "\\chi"], ["ψ", "\\psi"], ["ω", "\\omega"],
  ["Γ", "\\Gamma"], ["Δ", "\\Delta"], ["Θ", "\\Theta"], ["Λ", "\\Lambda"],
  ["Ξ", "\\Xi"], ["Π", "\\Pi"], ["Σ", "\\Sigma"], ["Υ", "\\Upsilon"],
  ["Φ", "\\Phi"], ["Ψ", "\\Psi"], ["Ω", "\\Omega"],
]);

const NAMED_SYMBOLS = new Map([
  ["Nat", "\\mathbb{N}"],
  ["Int", "\\mathbb{Z}"],
  ["Rat", "\\mathbb{Q}"],
  ["Real", "\\mathbb{R}"],
  ["Complex", "\\mathbb{C}"],
]);

const UNSUPPORTED_KEYWORDS = new Set([
  "let", "in", "if", "then", "else", "match", "with", "by", "do", "where",
  "have", "show", "suffices", "calc", "next", "termination_by", "decreasing_by",
  "return", "from", "as", "exact", "refine", "simp", "simpa", "rfl", "funext",
]);

const TOKEN_PATTERN = /\s+|∃!|∀|∃|→|↔|⟷|⟹|⟺|↦|⟶|∧|∨|¬|⊤|⊥|≤|≥|≠|∈|∉|∋|∌|∣|∥|∩|∪|⊆|⊂|⊇|⊃|⊓|⊔|⊕|⊗|×|∘|⋅|·|∑|∏|∫|∞|∂|∇|∅|≈|≃|≅|≡|∼|∝|ℕ|ℤ|ℚ|ℝ|ℂ|->|<->|=>|<=|>=|!=|:=|==|&&|\|\||\d+(?:\.\d+)?|[A-Za-z_][A-Za-z0-9_'.]*|[\p{L}\p{N}\p{M}][\p{L}\p{N}\p{M}_'.]*|[!#$%&*+\-\.\/:<=>?@\\^|~]{2,}|[(){}\[\],;:!?+\-*\/^=<>|]/gu;

function identifierToTex(token) {
  if (NAMED_SYMBOLS.has(token)) return NAMED_SYMBOLS.get(token);
  if (GREEK_MAP.has(token)) return GREEK_MAP.get(token);
  if (token === "Type" || token === "Sort" || token === "Prop") return "\\mathrm{" + token + "}";
  const escaped = token.replace(/[\\{}#$%&_]/g, "\\$&");
  return "\\mathrm{" + escaped + "}";
}

function tokenToTex(token) {
  if (/^\s+$/u.test(token)) return /[\r\n]/u.test(token) ? "\\\\" : "\\,";
  if (OPERATOR_MAP.has(token)) return OPERATOR_MAP.get(token);
  if (token === "fun") return "\\lambda";
  if (token === "(" || token === ")" || token === "[" || token === "]") return token;
  if (token === "{") return "\\{";
  if (token === "}") return "\\}";
  if (token === ",") return ",";
  if (token === ";") return ";";
  if (token === ":") return "\\mathrel{:}";
  if (token === ".") return ".";
  if (token === "|") return "\\mid";
  if (token === "!") return "\\lnot";
  if (/^\d+(?:\.\d+)?$/u.test(token)) return token;
  if (/^[A-Za-z_\p{L}\p{N}\p{M}][A-Za-z0-9_'.\p{L}\p{N}\p{M}]*$/u.test(token)) {
    if (UNSUPPORTED_KEYWORDS.has(token)) return null;
    return identifierToTex(token);
  }
  return null;
}

export function leanPrettyToTex(source) {
  if (typeof source !== "string" || source.length === 0) return null;
  const tokens = [];
  let cursor = 0;
  for (const match of source.matchAll(TOKEN_PATTERN)) {
    if (match.index !== cursor) return null;
    tokens.push(match[0]);
    cursor += match[0].length;
  }
  if (cursor !== source.length) return null;

  const pieces = [];
  for (const token of tokens) {
    const tex = tokenToTex(token);
    if (tex === null) return null;
    pieces.push(tex);
  }
  const tex = pieces.join("");
  return /[\r\n]/u.test(source) ? "\\begin{gathered}" + tex + "\\end{gathered}" : tex;
}

const mathJaxReady = new Promise((resolve) => {
  const script = document.querySelector("script[data-math-renderer]");
  if (!script) {
    resolve(false);
    return;
  }

  let settled = false;
  let pollId = null;
  let waitingForStartup = false;
  const finish = (available) => {
    if (settled) return;
    settled = true;
    if (pollId !== null) window.clearInterval(pollId);
    resolve(available);
  };
  const loaded = () => {
    const startup = window.MathJax?.startup?.promise;
    if (startup && typeof startup.then === "function") {
      if (waitingForStartup) return;
      waitingForStartup = true;
      startup.then(
        () => finish(typeof window.MathJax?.typesetPromise === "function"),
        () => finish(false),
      );
    } else {
      finish(typeof window.MathJax?.typesetPromise === "function");
    }
  };

  if (typeof window.MathJax?.typesetPromise === "function") loaded();
  else {
    script.addEventListener("load", loaded, { once: true });
    script.addEventListener("error", () => finish(false), { once: true });
    pollId = window.setInterval(() => {
      if (typeof window.MathJax?.typesetPromise === "function") loaded();
    }, 50);
  }
  window.setTimeout(() => finish(false), 8000);
});

export function renderLeanSourceFallback(container, source, reason) {
  container.replaceChildren();
  container.classList.add("math-fallback");
  if (reason) {
    const note = document.createElement("p");
    note.className = "math-fallback-note";
    note.textContent = reason;
    container.append(note);
  }
  const exact = document.createElement("pre");
  exact.textContent = source;
  container.append(exact);
}

export function renderLeanMath(container, source) {
  const tex = leanPrettyToTex(source);
  if (tex === null) {
    renderLeanSourceFallback(container, source, "Formula rendering is not available for this Lean syntax.");
    return;
  }

  container.classList.add("math-presentation");
  const formula = document.createElement("div");
  formula.className = "math-formula";
  formula.setAttribute("aria-label", "Mathematical rendering");
  formula.textContent = "Rendering formula…";
  container.append(formula);

  const exact = document.createElement("details");
  exact.className = "lean-source";
  const summary = document.createElement("summary");
  summary.textContent = "Lean notation";
  const pre = document.createElement("pre");
  pre.textContent = source;
  exact.append(summary, pre);
  container.append(exact);

  mathJaxReady.then(async (available) => {
    if (!container.isConnected) return;
    if (!available) {
      renderLeanSourceFallback(container, source, "Formula rendering is unavailable; showing Lean notation.");
      return;
    }
    try {
      formula.textContent = "\\[" + tex + "\\]";
      await window.MathJax.typesetPromise([formula]);
    } catch {
      if (typeof window.MathJax.typesetClear === "function") window.MathJax.typesetClear([formula]);
      renderLeanSourceFallback(container, source, "Formula rendering failed; showing Lean notation.");
    }
  });
}
