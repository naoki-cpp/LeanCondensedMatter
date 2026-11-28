export const ZOOM_STEP = 1.25;

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
