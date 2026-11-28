import { cameraProgress } from "./map-zoom.js";

export function createMapNavigation(width, height) {
  const home = { x: width / 2, y: height / 2, zoom: 1 };
  let view = { ...home };
  let active = null;
  let selected = null;
  let previousScope = null;
  let transition = null;
  let blend = 1;

  function regionView(region) {
    if (!region.children.length) {
      return { x: region.x, y: region.y, zoom: height / (3 * region.radius) };
    }
    const extents = [...region.children, ...region.points.filter((point) => point.region === region)];
    const left = Math.min(...extents.map(({ x, radius = 0 }) => x - radius));
    const right = Math.max(...extents.map(({ x, radius = 0 }) => x + radius));
    const top = Math.min(...extents.map(({ y, radius = 0 }) => y - radius));
    const bottom = Math.max(...extents.map(({ y, radius = 0 }) => y + radius));
    const zoom = Math.min((width - 104) / (right - left), (height - 140) / (bottom - top));
    return { x: (left + right) / 2, y: (top + bottom) / 2, zoom };
  }

  function positionInScope(point, scope) {
    for (let candidate = scope; candidate; candidate = candidate.parent) {
      const position = point.positions.get(candidate);
      if (position) return position;
    }
    return point.positions.get(null);
  }

  function screen(x, y) {
    return [(x - view.x) * view.zoom + home.x, (y - view.y) * view.zoom + home.y];
  }

  function stop() {
    transition = null;
    blend = 1;
  }

  function setRegion(region) {
    previousScope = active;
    active = region;
    selected = null;
  }

  function open(region, animate, toParent = false) {
    stop();
    setRegion(region);
    const target = regionView(region);
    moveTo(target, animate, toParent);
  }

  function moveTo(target, animate, toParent = false) {
    if (animate && (view.x !== target.x || view.y !== target.y || view.zoom !== target.zoom)) {
      blend = 0;
      transition = { start: { ...view }, target, toParent };
    } else view = { ...target };
  }

  function reset(animate = false) {
    stop();
    setRegion(null);
    moveTo(home, animate);
  }

  return {
    get view() { return view; },
    get active() { return active; },
    get selected() { return selected; },
    get animating() { return transition !== null; },
    get overview() { return view.zoom <= 1.5; },
    screen,
    pointOnScreen(point) {
      const scope = view.zoom > 1.5 || transition ? active : null;
      const to = positionInScope(point, scope);
      if (blend === 1) return screen(to.x, to.y);
      const from = positionInScope(point, previousScope);
      return screen(from.x + (to.x - from.x) * blend, from.y + (to.y - from.y) * blend);
    },
    open,
    stop,
    reset,
    select(point) {
      stop();
      setRegion(point.region);
      selected = point;
      view = { x: point.x, y: point.y, zoom: Math.max(height / (3 * point.region.radius), view.zoom) };
    },
    step(now) {
      if (!transition) return;
      transition.startedAt ??= now;
      const { start, target, startedAt } = transition;
      const eased = cameraProgress(now - startedAt);
      blend = eased;
      view = {
        x: start.x + (target.x - start.x) * eased,
        y: start.y + (target.y - start.y) * eased,
        zoom: start.zoom * (target.zoom / start.zoom) ** eased,
      };
      if (eased === 1) stop();
    },
    pan(dx, dy, origin = view) {
      stop();
      view = { ...view, x: origin.x + dx / view.zoom, y: origin.y + dy / view.zoom };
    },
    zoom(factor, x = home.x, y = home.y, animate = true) {
      if (factor < 1 && transition?.toParent) return false;
      stop();
      const limit = Math.max(24, active ? height / active.radius : 24, view.zoom);
      const next = Math.max(1, Math.min(limit, view.zoom * factor));
      if (factor < 1 && active?.parent) {
        const threshold = Math.max(regionView(active.parent).zoom, regionView(active).zoom / 1.5);
        if (next <= threshold * (1 + Number.EPSILON)) {
          open(active.parent, animate, true);
          return true;
        }
      } else if (factor < 1 && active && next <= 1.5) {
        reset(animate);
        return true;
      }
      view = {
        x: view.x + (x - home.x) * (1 / view.zoom - 1 / next),
        y: view.y + (y - home.y) * (1 / view.zoom - 1 / next),
        zoom: next,
      };
      return true;
    },
  };
}
