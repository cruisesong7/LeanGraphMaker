// widget/widget_visualize.js — Issue #9
// Read-only visualization widget: takes a graph6 string from Lean and renders it.
// UI styling matches widget_graph.js so the two widgets feel uniform.
import * as React from "react";
var e = React.createElement;

function parseGraph6(g6, canvasWidth, canvasHeight) {
  if (!g6 || g6 === "?") return { nodes: [], edges: new Map() };
  const n = g6.charCodeAt(0) - 63;
  if (n < 0 || n > 62) return { nodes: [], edges: new Map() };
  const payload = g6.slice(1);
  const bits = [];
  for (let i = 0; i < payload.length; i++) {
    let chunk = payload.charCodeAt(i) - 63;
    for (let j = 5; j >= 0; j--) bits.push((chunk >> j) & 1);
  }
  const edges = new Map();
  let bitIndex = 0;
  for (let j = 1; j < n; j++) {
    for (let i = 0; i < j; i++) {
      if (bits[bitIndex] === 1) edges.set(`${i}-${j}`, { color: "red" });
      bitIndex++;
    }
  }
  const nodes = [];
  const radius = Math.min(canvasWidth, canvasHeight) / 2 - 40;
  const cx = canvasWidth / 2;
  const cy = canvasHeight / 2;
  for (let i = 0; i < n; i++) {
    const angle = (2 * Math.PI * i) / n;
    nodes.push({ id: i, x: cx + radius * Math.cos(angle), y: cy + radius * Math.sin(angle) });
  }
  return { nodes, edges };
}

function clamp(v, lo, hi) { return Math.max(lo, Math.min(hi, v)); }

var btnStyle = {
  border: "1px solid rgba(255, 255, 255, 0.15)",
  background: "rgba(255, 255, 255, 0.08)",
  color: "inherit",
  padding: "6px 10px",
  borderRadius: "6px",
  cursor: "pointer",
  fontSize: "12px"
};

function widget_visualize_default(props) {
  const canvasRef = React.useRef(null);
  const [canvasSize] = React.useState({ width: 600, height: 400 });
  const g6 = props.graph6 || "?";
  const initial = React.useMemo(() => parseGraph6(g6, canvasSize.width, canvasSize.height), [g6, canvasSize]);
  const [nodes, setNodes] = React.useState(initial.nodes);
  const [edges] = React.useState(initial.edges);
  const [draggingNodeId, setDraggingNodeId] = React.useState(null);
  const [dragOffset, setDragOffset] = React.useState({ x: 0, y: 0 });

  React.useEffect(() => {
    setNodes(initial.nodes);
  }, [initial]);

  const draw = React.useCallback(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const ctx = canvas.getContext("2d");
    if (!ctx) return;
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.save();
    ctx.lineWidth = 2;
    ctx.strokeStyle = "rgba(248, 113, 113, 0.9)";
    edges.forEach((_, key) => {
      const [a, b] = key.split("-").map(Number);
      const na = nodes.find((n) => n.id === a);
      const nb = nodes.find((n) => n.id === b);
      if (!na || !nb) return;
      ctx.beginPath();
      ctx.moveTo(na.x, na.y);
      ctx.lineTo(nb.x, nb.y);
      ctx.stroke();
    });
    nodes.forEach((node, index) => {
      const radius = 16;
      const grad = ctx.createRadialGradient(node.x - 6, node.y - 6, 4, node.x, node.y, radius + 2);
      grad.addColorStop(0, "#34d399");
      grad.addColorStop(1, "#10b981");
      ctx.fillStyle = grad;
      ctx.beginPath();
      ctx.arc(node.x, node.y, radius, 0, Math.PI * 2);
      ctx.fill();
      ctx.lineWidth = 2;
      ctx.strokeStyle = "rgba(255,255,255,0.6)";
      ctx.stroke();
      ctx.fillStyle = "#0b1224";
      ctx.font = "bold 13px system-ui, sans-serif";
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText(index.toString(), node.x, node.y);
    });
    ctx.restore();
  }, [nodes, edges]);

  React.useEffect(() => { draw(); }, [draw]);

  const findNodeAt = (x, y) => {
    const radius = 18;
    return nodes.find((node) => Math.hypot(node.x - x, node.y - y) <= radius);
  };
  const canvasCoords = (e2) => {
    const canvas = canvasRef.current;
    if (!canvas) return null;
    const rect = canvas.getBoundingClientRect();
    const sx = canvas.width / rect.width;
    const sy = canvas.height / rect.height;
    return { x: (e2.clientX - rect.left) * sx, y: (e2.clientY - rect.top) * sy, canvas };
  };
  const onMouseDown = (e2) => {
    const c = canvasCoords(e2); if (!c) return;
    const node = findNodeAt(c.x, c.y);
    if (node) {
      setDraggingNodeId(node.id);
      setDragOffset({ x: node.x - c.x, y: node.y - c.y });
    }
  };
  const onMouseMove = (e2) => {
    if (draggingNodeId === null) return;
    const c = canvasCoords(e2); if (!c) return;
    setNodes((prev) => prev.map((node) => node.id === draggingNodeId
      ? { ...node, x: clamp(c.x + dragOffset.x, 20, c.canvas.width - 20),
                   y: clamp(c.y + dragOffset.y, 20, c.canvas.height - 20) }
      : node));
  };
  const onMouseUp = () => setDraggingNodeId(null);

  const applyCircle = () => {
    const n = nodes.length; if (n === 0) return;
    const radius = Math.min(canvasSize.width, canvasSize.height) / 2 - 40;
    const cx = canvasSize.width / 2, cy = canvasSize.height / 2;
    setNodes((prev) => prev.map((node, i) => {
      const a = (2 * Math.PI * i) / n;
      return { ...node, x: cx + radius * Math.cos(a), y: cy + radius * Math.sin(a) };
    }));
  };
  const applySpring = () => {
    const n = nodes.length; if (n === 0) return;
    const area = canvasSize.width * canvasSize.height;
    const k = Math.sqrt(area / (n + 1e-3));
    let temperature = Math.min(canvasSize.width, canvasSize.height) / 8;
    const current = nodes.map((x) => ({ ...x }));
    const idToIdx = new Map(current.map((node, i) => [node.id, i]));
    for (let iter = 0; iter < 250; iter++) {
      const disp = current.map(() => ({ x: 0, y: 0 }));
      for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
        const dx = current[j].x - current[i].x, dy = current[j].y - current[i].y;
        const dist = Math.hypot(dx, dy) + 0.01;
        const f = (k * k) / dist;
        disp[i].x -= (f * dx) / dist; disp[i].y -= (f * dy) / dist;
        disp[j].x += (f * dx) / dist; disp[j].y += (f * dy) / dist;
      }
      edges.forEach((_, key) => {
        const [aId, bId] = key.split("-").map(Number);
        const i = idToIdx.get(aId), j = idToIdx.get(bId);
        if (i === void 0 || j === void 0) return;
        const dx = current[j].x - current[i].x, dy = current[j].y - current[i].y;
        const dist = Math.hypot(dx, dy) + 0.01;
        const f = (dist * dist) / k;
        disp[i].x += (f * dx) / dist; disp[i].y += (f * dy) / dist;
        disp[j].x -= (f * dx) / dist; disp[j].y -= (f * dy) / dist;
      });
      for (let i = 0; i < n; i++) {
        const dx = disp[i].x, dy = disp[i].y;
        const dist = Math.hypot(dx, dy) || 1;
        const limited = Math.min(temperature, dist);
        current[i].x = clamp(current[i].x + (dx / dist) * limited, 20, canvasSize.width - 20);
        current[i].y = clamp(current[i].y + (dy / dist) * limited, 20, canvasSize.height - 20);
      }
      temperature *= 0.95; if (temperature < 0.5) break;
    }
    setNodes(current);
  };

  const edgeCount = edges.size;
  return e("div", { style: {
    fontFamily: "system-ui, sans-serif",
    background: "#0f172a", color: "#e2e8f0",
    borderRadius: "8px", overflow: "hidden"
  } }, [
    e("div", { style: {
      padding: "12px 16px",
      background: "rgba(15, 23, 42, 0.75)",
      borderBottom: "1px solid rgba(255, 255, 255, 0.08)"
    } }, [
      e("h3", { style: { margin: "0 0 8px 0", fontSize: "16px" } }, "Graph Visualizer"),
      e("div", { style: { display: "flex", gap: "8px", flexWrap: "wrap", alignItems: "center" } }, [
        e("span", { style: {
          padding: "4px 8px", background: "rgba(255,255,255,0.08)",
          borderRadius: "999px", fontSize: "12px",
          border: "1px solid rgba(255,255,255,0.15)"
        } }, `Nodes: ${nodes.length}`),
        e("span", { style: {
          padding: "4px 8px", background: "rgba(255,255,255,0.08)",
          borderRadius: "999px", fontSize: "12px",
          border: "1px solid rgba(255,255,255,0.15)"
        } }, `Edges: ${edgeCount}`),
        e("button", { onClick: applyCircle, style: btnStyle }, "Circle layout"),
        e("button", { onClick: applySpring, style: btnStyle }, "Spring layout")
      ])
    ]),
    e("canvas", {
      ref: canvasRef,
      width: canvasSize.width,
      height: canvasSize.height,
      onMouseDown, onMouseMove, onMouseUp,
      style: {
        display: "block", width: "100%",
        background: "radial-gradient(circle at 50% 50%, rgba(255,255,255,0.04), transparent 60%), #0b1224",
        cursor: draggingNodeId !== null ? "grabbing" : "grab"
      }
    }),
    e("div", { style: {
      padding: "12px 16px",
      background: "rgba(10,14,26,0.85)",
      borderTop: "1px solid rgba(255,255,255,0.08)"
    } }, [
      e("div", { style: { fontSize: "11px", color: "#cbd5e1", marginBottom: "6px" } },
        "Read-only visualization of a graph6 string. Drag nodes to reposition."),
      e("div", { style: {
        fontSize: "11px", fontFamily: "monospace",
        color: "#94a3b8", wordBreak: "break-all"
      } }, `graph6: ${g6}`)
    ])
  ]);
}

export { widget_visualize_default as default };
