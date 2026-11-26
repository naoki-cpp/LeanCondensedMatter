# Declaration and import explorer

The browser explorer uses the same graph rendering flow for declarations and module imports.

`docs-site/graph-presentation.js` owns mode-specific node colors, edge styles, and legend entries. Its `createGraphPresentation(mode)` interface returns `node`, `edge`, and `legend`. Legend entries use the same rules as graph marks; HTML and CSS do not maintain separate category lists or palettes. Legend samples increase line opacity for readability at their small size.

`docs-site/graph-layout.js` owns neighborhood traversal, tree-parent selection, density spacing, and radial placement. Its `buildGraphScene(catalog, options)` interface takes the catalog, root, direction, depth, filter predicate, and optional node cap. It returns scene geometry and truncation information without accessing browser state or mutating the catalog. Missing references are ignored, filters prune traversal, and the root remains visible.

`docs-site/graph.js` owns browser state, data loading, navigation, DOM rendering, selection, and viewport interaction. It supplies the filter predicate and renders the results from the layout and presentation modules.

Tests exercise the same presentation and layout interfaces as the browser. Presentation tests check that declaration and import legends match drawing rules. Layout tests cover cyclic references, missing neighbors, filtering, direction, determinism, and truncation.
