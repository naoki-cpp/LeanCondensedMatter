# Declaration and import explorer

The browser explorer uses the same graph rendering flow for declarations and module imports.

`docs-site/graph-presentation.js` owns mode-specific node colors, edge styles, and legend entries. Its `createGraphPresentation(mode)` interface returns `node`, `edge`, and `legend`. Legend entries use the same rules as graph marks; HTML and CSS do not maintain separate category lists or palettes. Legend samples increase line opacity for readability at their small size.

`docs-site/graph-layout.js` owns neighborhood traversal, tree-parent selection, density spacing, and radial placement. Its `buildGraphScene(catalog, options)` interface takes the catalog, root, direction, depth, filter predicate, and optional node cap. It returns scene geometry and truncation information without accessing browser state or mutating the catalog. Missing references are ignored, filters prune traversal, and the root remains visible.

`docs-site/declaration-hierarchy.js` indexes module paths, direct and descendant declarations, and counts. The overview uses the full hierarchy for module navigation and a filtered hierarchy for map points and directional dependency counts between sibling regions.

`docs-site/declaration-visibility.js` supplies the filtered declaration set to search, map hierarchy construction, and graph traversal. The dependency graph keeps its selected root even when traversal excludes that declaration.

`docs-site/map-navigation.js` owns the map camera, active scope, selected declaration, and transitions to parent regions. `docs-site/research-map.js` draws the canvas, handles input, and supplies animation timestamps.

`docs-site/map-scene.js` lays out regions and points and resolves visible labels and pointer targets against the same camera projection.

`docs-site/explorer-composition.js` moves the shared tablist and controls between the overview, declaration graph, and imports graph. It applies asynchronously prepared overview content only while its request is current.
It mounts and disposes the map as views change so resize observation and camera work are scoped to the active map.

`docs-site/explorer-location.js` translates between explorer views and URL/history entries, including the declaration graph's return destination.
Map region changes update the current history entry, which also stores the selected declaration.

`docs-site/map-zoom.js` owns shared zoom input, timing, and animation frame scheduling. Canvas and SVG retain their own coordinate transforms.

`docs-site/declaration-details.js` supplies statement and definition body display, source links, and relation counts to both declaration views. Each view resolves the relations it can open.

`docs-site/graph.js` owns browser state, data loading, navigation, DOM rendering, selection, and viewport interaction. It supplies the filter predicate and renders the results from the layout and presentation modules.

Tests exercise the same presentation and layout interfaces as the browser. Presentation tests check that declaration and import legends match drawing rules. Layout tests cover cyclic references, missing neighbors, filtering, direction, determinism, and truncation.
