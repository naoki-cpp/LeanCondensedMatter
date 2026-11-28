const goldenAngle = Math.PI * (3 - Math.sqrt(5));

export function createMapScene(children, hierarchy, width, height) {
  const byName = new Map();
  const largest = Math.max(1, ...children.map((child) => child.entries.length));
  const columns = Math.min(3, Math.max(1, children.length));
  const rows = Math.max(1, Math.ceil(children.length / columns));
  const spacing = Math.min(91, (height / rows - 46) / 2);
  const allRegions = [];
  const regionByModule = new Map();
  function placeCloud(points, scope, x, y, radius) {
    points.forEach((point, i) => {
      const distance = radius * .94 * Math.sqrt(i / points.length);
      const angle = goldenAngle * i;
      point.positions.set(scope, { x: x + distance * Math.cos(angle), y: y + distance * Math.sin(angle) });
    });
  }
  function buildRegion(module, x, y, radius, parent = null) {
    const name = module.name.replace(/([a-z])([A-Z])/g, "$1 $2");
    const region = { name, moduleName: module.path, module, x, y, radius, parent, children: [] };
    allRegions.push(region);
    regionByModule.set(module, region);
    const ordered = [...module.children].sort(([a], [b]) => a.localeCompare(b));
    if (module.declarations.length) ordered.unshift(["", null]);
    const cellColumns = Math.max(1, Math.ceil(Math.sqrt(ordered.length)));
    const cellRows = Math.ceil(ordered.length / cellColumns);
    const cell = region.radius * Math.SQRT2 / Math.max(cellColumns, cellRows);
    region.points = ordered.flatMap(([key, childModule], i) => {
      const grouped = ordered.length > 1;
      const gx = grouped ? x + ((i % cellColumns) - (cellColumns - 1) / 2) * cell : x;
      const gy = grouped ? y + (Math.floor(i / cellColumns) - (cellRows - 1) / 2) * cell : y;
      const groupRadius = grouped ? cell * .34 : region.radius * .75;
      let points;
      if (key) {
        const child = buildRegion(childModule, gx, gy, groupRadius, region);
        region.children.push(child);
        points = child.points;
      } else {
        points = module.declarations.map((entry) => {
          const point = { entry, region, positions: new Map() };
          byName.set(entry.name, point);
          return point;
        });
      }
      placeCloud(points, region, gx, gy, groupRadius);
      if (!key) for (const point of points) Object.assign(point, point.positions.get(region));
      return points;
    });
    return region;
  }
  const regions = children.map((child, index) => {
    const x = ((index % columns) + .5) * width / columns + (Math.floor(index / columns) % 2 ? 20 : -20);
    const y = (Math.floor(index / columns) + .44) * height / rows;
    const radius = spacing * Math.sqrt(child.entries.length / largest);
    const region = buildRegion(child, x, y, radius);
    placeCloud(region.points, null, x, y, radius);
    return region;
  });

  const points = [...byName.values()];
  const emptyBundles = [];
  const bundleCache = new Map();
  function bundlesFor(module) {
    if (!module) return emptyBundles;
    if (!bundleCache.has(module)) {
      bundleCache.set(module, hierarchy.bundles(module).map(({ a, b, ab, ba }) => ({
        a: regionByModule.get(a), b: regionByModule.get(b), ab, ba,
      })));
    }
    return bundleCache.get(module);
  }
  function pointAt(x, y, pointOnScreen) {
    let nearest = null;
    let best = 10;
    for (const point of points) {
      const [px, py] = pointOnScreen(point);
      const distance = Math.hypot(x - px, y - py);
      if (distance < best) { best = distance; nearest = point; }
    }
    return nearest;
  }

  return {
    allRegions,
    points,
    point: (name) => byName.get(name),
    region: (moduleName) => regionByModule.get(hierarchy.find(moduleName)),
    frame(navigation) {
      const { active, overview, screen, pointOnScreen, view } = navigation;
      const labels = overview || !active ? regions : active.children;
      const outlines = allRegions.filter((region) => (!region.parent || (!overview &&
        (active === region || active === region.parent))) &&
        (overview || region !== active || !region.children.length));
      function regionAt(x, y) {
        return labels.find((region) => {
          const [px, py] = screen(region.x, region.y);
          const hitRadius = overview ? region.radius + 14 : region.radius * view.zoom + 5;
          return Math.hypot(x - px, y - py) <= hitRadius;
        });
      }
      return {
        labels, outlines, screen, pointOnScreen,
        bundles: bundlesFor(overview ? hierarchy.root : active?.module),
        hoverPoint(x, y) {
          return !overview && regionAt(x, y) ? null : pointAt(x, y, pointOnScreen);
        },
        target(x, y) {
          const region = regionAt(x, y);
          if (region) return { region };
          return overview ? null : { point: pointAt(x, y, pointOnScreen) };
        },
      };
    },
  };
}
