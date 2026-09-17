const viewport = document.querySelector("#graph-viewport");

if (viewport) {
  const pointers = new Map();
  const ZOOM_STEP = 0.13;
  let previousDistance = null;
  let zoomAccumulator = 0;
  let suppressClickUntil = 0;
  let pinching = false;
  let forwardingPointerEvent = false;

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

  function forwardPointerEvent(type, pointerId, point) {
    forwardingPointerEvent = true;
    try {
      viewport.dispatchEvent(new PointerEvent(type, {
        bubbles: true,
        cancelable: true,
        pointerId,
        pointerType: "touch",
        clientX: point.x,
        clientY: point.y,
        buttons: type === "pointerdown" ? 1 : 0,
      }));
    } finally {
      forwardingPointerEvent = false;
    }
  }

  function resetPinch() {
    previousDistance = null;
    zoomAccumulator = 0;
  }

  function startPinch() {
    const entries = [...pointers.entries()];
    if (entries.length < 2) return;
    const [[dragPointerId, first], [, second]] = entries;
    forwardPointerEvent("pointercancel", dragPointerId, first);
    previousDistance = distance(first, second);
    zoomAccumulator = 0;
    pinching = true;
    suppressClickUntil = performance.now() + 400;
    viewport.classList.remove("dragging");
  }

  function restartDrag() {
    if (pointers.size !== 1) return;
    const [[pointerId, point]] = pointers.entries();
    forwardPointerEvent("pointerdown", pointerId, point);
  }

  viewport.addEventListener("pointerdown", (event) => {
    if (forwardingPointerEvent || event.pointerType !== "touch") return;
    pointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
    if (pointers.size < 2) return;

    event.preventDefault();
    event.stopImmediatePropagation();
    startPinch();
  }, { capture: true, passive: false });

  viewport.addEventListener("pointermove", (event) => {
    if (forwardingPointerEvent || event.pointerType !== "touch" || !pointers.has(event.pointerId)) return;
    pointers.set(event.pointerId, { x: event.clientX, y: event.clientY });

    if (!pinching || pointers.size < 2) return;

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
    if (forwardingPointerEvent || event.pointerType !== "touch") return;
    const wasPinching = pinching;
    pointers.delete(event.pointerId);

    if (pointers.size >= 2) {
      startPinch();
      return;
    }

    resetPinch();
    pinching = false;
    if (wasPinching && pointers.size === 1) restartDrag();
  };

  viewport.addEventListener("pointerup", endPointer, { capture: true });
  viewport.addEventListener("pointercancel", endPointer, { capture: true });

  viewport.addEventListener("click", (event) => {
    if (performance.now() >= suppressClickUntil) return;
    event.preventDefault();
    event.stopImmediatePropagation();
  }, { capture: true });
}
