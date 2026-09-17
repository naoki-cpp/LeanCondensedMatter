const viewport = document.querySelector("#graph-viewport");

if (viewport) {
  const pointers = new Map();
  const ZOOM_STEP = 0.13;
  let previousDistance = null;
  let zoomAccumulator = 0;
  let suppressClickUntil = 0;

  function distance(a, b) {
    return Math.hypot(a.x - b.x, a.y - b.y);
  }

  function midpoint(a, b) {
    return {
      x: (a.x + b.x) / 2,
      y: (a.y + b.y) / 2,
    };
  }

  function dispatchZoom(deltaY, point) {
    viewport.dispatchEvent(new WheelEvent("wheel", {
      bubbles: true,
      cancelable: true,
      clientX: point.x,
      clientY: point.y,
      deltaY,
    }));
  }

  function resetPinch() {
    previousDistance = null;
    zoomAccumulator = 0;
  }

  viewport.addEventListener("pointerdown", (event) => {
    if (event.pointerType !== "touch") return;
    pointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
  }, { capture: true });

  viewport.addEventListener("pointermove", (event) => {
    if (event.pointerType !== "touch" || !pointers.has(event.pointerId)) return;
    pointers.set(event.pointerId, { x: event.clientX, y: event.clientY });

    if (pointers.size < 2) {
      resetPinch();
      return;
    }

    event.preventDefault();
    event.stopImmediatePropagation();
    suppressClickUntil = performance.now() + 400;

    const [first, second] = [...pointers.values()];
    const currentDistance = distance(first, second);
    if (currentDistance <= 0) return;

    if (previousDistance !== null && previousDistance > 0) {
      zoomAccumulator += Math.log(currentDistance / previousDistance);
      const center = midpoint(first, second);

      while (zoomAccumulator >= ZOOM_STEP) {
        dispatchZoom(-1, center);
        zoomAccumulator -= ZOOM_STEP;
      }
      while (zoomAccumulator <= -ZOOM_STEP) {
        dispatchZoom(1, center);
        zoomAccumulator += ZOOM_STEP;
      }
    }

    previousDistance = currentDistance;
  }, { capture: true, passive: false });

  const endPointer = (event) => {
    if (event.pointerType !== "touch") return;
    pointers.delete(event.pointerId);
    if (pointers.size < 2) resetPinch();
  };

  viewport.addEventListener("pointerup", endPointer, { capture: true });
  viewport.addEventListener("pointercancel", endPointer, { capture: true });

  viewport.addEventListener("click", (event) => {
    if (performance.now() >= suppressClickUntil) return;
    event.preventDefault();
    event.stopImmediatePropagation();
  }, { capture: true });
}
