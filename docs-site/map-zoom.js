export const ZOOM_STEP = 1.25;
const CAMERA_DURATION = 420;

export function canAnimateCamera() {
  return typeof requestAnimationFrame === "function" &&
    !window.matchMedia?.("(prefers-reduced-motion: reduce)").matches;
}

export function cameraProgress(elapsed) {
  const t = Math.min(1, elapsed / CAMERA_DURATION);
  return t * t * (3 - 2 * t);
}

export function zoomFactorForKey(key) {
  if (key === "+" || key === "=") return ZOOM_STEP;
  if (key === "-" || key === "−") return 1 / ZOOM_STEP;
  return null;
}

export function zoomFactorForWheel({ ctrlKey, metaKey, deltaY, deltaMode }) {
  if ((!ctrlKey && !metaKey) || !deltaY) return null;
  const pixels = deltaY * (deltaMode === 1 ? 16 : deltaMode === 2 ? 100 : 1);
  return Math.exp(-Math.max(-80, Math.min(80, pixels)) * 0.008);
}
