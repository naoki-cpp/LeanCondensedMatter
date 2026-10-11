export function curvedEdgePath(source, target, cx, cy) {
  const middleRadius = (source.radius + target.radius) / 2;
  const sourceAngle = source.radius === 0 ? target.angle : source.angle;
  const targetAngle = target.radius === 0 ? source.angle : target.angle;
  const dx = target.x - source.x;
  const dy = target.y - source.y;
  const lengthSquared = dx * dx + dy * dy;
  function controlPoint(angle, minProgress, maxProgress) {
    const x = cx + middleRadius * Math.cos(angle);
    const y = cy + middleRadius * Math.sin(angle);
    if (lengthSquared === 0) return { x: source.x, y: source.y };
    const progress = ((x - source.x) * dx + (y - source.y) * dy) / lengthSquared;
    const boundedProgress = Math.min(maxProgress, Math.max(minProgress, progress));
    // Ordered projections keep the whole Bezier curve moving toward its target.
    return { x: x + (boundedProgress - progress) * dx, y: y + (boundedProgress - progress) * dy };
  }
  const c1 = controlPoint(sourceAngle, 0, 0.5);
  const c2 = controlPoint(targetAngle, 0.5, 1);
  return `M ${source.x} ${source.y} C ${c1.x} ${c1.y}, ${c2.x} ${c2.y}, ${target.x} ${target.y}`;
}
