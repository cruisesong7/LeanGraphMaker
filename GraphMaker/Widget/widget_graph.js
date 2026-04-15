// widget/widget_graph.ts
import { RpcContext, EditorContext, mapRpcError } from "@leanprover/infoview";
import * as React from "react";
var e = React.createElement;
function parseGraph6(g6, canvasWidth, canvasHeight) {
  if (!g6 || g6 === "?") return { nodes: [], edges: /* @__PURE__ */ new Map() };
  const n = g6.charCodeAt(0) - 63;
  if (n < 0 || n > 62) return { nodes: [], edges: /* @__PURE__ */ new Map() };
  const payload = g6.slice(1);
  const bits = [];
  for (let i = 0; i < payload.length; i++) {
    let chunk = payload.charCodeAt(i) - 63;
    for (let j = 5; j >= 0; j--) {
      bits.push(chunk >> j & 1);
    }
  }
  const edges = /* @__PURE__ */ new Map();
  let bitIndex = 0;
  for (let j = 1; j < n; j++) {
    for (let i = 0; i < j; i++) {
      if (bits[bitIndex] === 1) {
        edges.set(`${i}-${j}`, { color: "red" });
      }
      bitIndex++;
    }
  }
  const nodes = [];
  const radius = Math.min(canvasWidth, canvasHeight) / 2 - 40;
  const cx = canvasWidth / 2;
  const cy = canvasHeight / 2;
  for (let i = 0; i < n; i++) {
    const angle = 2 * Math.PI * i / n;
    nodes.push({
      id: i,
      x: cx + radius * Math.cos(angle),
      y: cy + radius * Math.sin(angle)
    });
  }
  return { nodes, edges };
}
function toGraph6(nodes, edges) {
  const n = nodes.length;
  if (n === 0) return "?";
  if (n > 62) return "?";
  const header = String.fromCharCode(n + 63);
  const bits = [];
  for (let j = 1; j < n; j++) {
    for (let i = 0; i < j; i++) {
      const key = sortedKey(nodes[i].id, nodes[j].id);
      const edge = edges.get(key);
      bits.push(edge && edge.color === "red" ? 1 : 0);
    }
  }
  while (bits.length % 6 !== 0) bits.push(0);
  let payload = "";
  for (let i = 0; i < bits.length; i += 6) {
    const chunk = bits.slice(i, i + 6).reduce((acc, b) => acc << 1 | b, 0);
    payload += String.fromCharCode(chunk + 63);
  }
  return header + payload;
}
function sortedKey(aId, bId) {
  return aId < bId ? `${aId}-${bId}` : `${bId}-${aId}`;
}
function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}
function drawArrowhead(ctx, fromX, fromY, toX, toY, nodeRadius) {
  const angle = Math.atan2(toY - fromY, toX - fromX);
  const tipX = toX - nodeRadius * Math.cos(angle);
  const tipY = toY - nodeRadius * Math.sin(angle);
  const headLen = 14;
  const headAngle = Math.PI / 7;
  ctx.beginPath();
  ctx.moveTo(tipX, tipY);
  ctx.lineTo(tipX - headLen * Math.cos(angle - headAngle), tipY - headLen * Math.sin(angle - headAngle));
  ctx.lineTo(tipX - headLen * Math.cos(angle + headAngle), tipY - headLen * Math.sin(angle + headAngle));
  ctx.closePath();
  ctx.fill();
}
function cloneEdges(edges) {
  const m = new Map();
  edges.forEach((val, key) => m.set(key, { ...val }));
  return m;
}
function snapshotState(nodes, edges) {
  return {
    nodes: nodes.map((n) => ({ ...n })),
    edges: cloneEdges(edges)
  };
}

var btnStyle = {
  border: "1px solid rgba(255, 255, 255, 0.15)",
  background: "rgba(255, 255, 255, 0.08)",
  color: "inherit",
  padding: "6px 10px",
  borderRadius: "6px",
  cursor: "pointer",
  fontSize: "12px"
};

function widget_graph_default(props) {
  const rs = React.useContext(RpcContext);
  const ec = React.useContext(EditorContext);
  const canvasRef = React.useRef(null);
  const [canvasSize, setCanvasSize] = React.useState({ width: 600, height: 400 });
  const initialGraph = parseGraph6(props.graph6 || "?", canvasSize.width, canvasSize.height);
  const [nodes, setNodes] = React.useState(initialGraph.nodes);
  const [edges, setEdges] = React.useState(initialGraph.edges);
  const [status, setStatus] = React.useState("Ready");
  const [range, _] = React.useState(props.replaceRange);
  const [graphMode, setGraphMode] = React.useState("simple");
  const [directed, setDirected] = React.useState(false);
  const [weighted, setWeighted] = React.useState(false);
  const [nextWeight, setNextWeight] = React.useState(1);
  const [selectedNodeId, setSelectedNodeId] = React.useState(null);
  const [draggingNodeId, setDraggingNodeId] = React.useState(null);
  const [dragOffset, setDragOffset] = React.useState({ x: 0, y: 0 });
  const [dragStart, setDragStart] = React.useState({ x: 0, y: 0 });
  const [isDragging, setIsDragging] = React.useState(false);
  const dragHistorySavedRef = React.useRef(false);
  // Issue #11: subgraph highlight mode
  const [subgraphMode, setSubgraphMode] = React.useState(false);
  const [selectedSubVertices, setSelectedSubVertices] = React.useState(() => new Set());
  const [selectedSubEdges, setSelectedSubEdges] = React.useState(() => new Set());
  const [marquee, setMarquee] = React.useState(null); // {x0,y0,x1,y1} while dragging

  // Undo history (Issue #4)
  const historyRef = React.useRef([]);
  const pushHistory = () => {
    historyRef.current.push(snapshotState(nodes, edges));
    if (historyRef.current.length > 100) historyRef.current.shift();
  };
  const undo = () => {
    if (historyRef.current.length === 0) {
      setStatus("Nothing to undo");
      return;
    }
    const prev = historyRef.current.pop();
    setNodes(prev.nodes);
    setEdges(prev.edges);
    setSelectedNodeId(null);
    setStatus("Undone");
  };

  // Ctrl+Z handler
  React.useEffect(() => {
    const handler = (ev) => {
      if ((ev.ctrlKey || ev.metaKey) && ev.key === "z") {
        ev.preventDefault();
        undo();
      }
    };
    window.addEventListener("keydown", handler);
    return () => window.removeEventListener("keydown", handler);
  });

  const graph6String = React.useMemo(() => toGraph6(nodes, edges), [nodes, edges]);
  const edgeCount = React.useMemo(() => {
    let count = 0;
    edges.forEach(({ color }) => {
      if (color === "red") count++;
    });
    return count;
  }, [edges]);
  const draw = React.useCallback(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const ctx = canvas.getContext("2d");
    if (!ctx) return;
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.save();
    ctx.lineWidth = 2;
    edges.forEach((edgeData, key) => {
      const { color } = edgeData;
      if (graphMode === "simple" && color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const na = nodes.find((n) => n.id === a);
      const nb = nodes.find((n) => n.id === b);
      if (!na || !nb) return;
      ctx.strokeStyle = color === "blue" ? "rgba(96, 165, 250, 0.85)" : "rgba(248, 113, 113, 0.9)";
      ctx.beginPath();
      // For directed edges, determine source/target
      let fromNode = na;
      let toNode = nb;
      if (directed && edgeData.from !== undefined) {
        fromNode = nodes.find((n) => n.id === edgeData.from) || na;
        toNode = nodes.find((n) => n.id === edgeData.to) || nb;
      }
      // Subgraph highlight: yellow halo under selected edges (Issue #11)
      if (subgraphMode && selectedSubEdges.has(key)) {
        ctx.save();
        ctx.strokeStyle = "rgba(253, 224, 71, 0.9)";
        ctx.lineWidth = 6;
        ctx.beginPath();
        ctx.moveTo(fromNode.x, fromNode.y);
        ctx.lineTo(toNode.x, toNode.y);
        ctx.stroke();
        ctx.restore();
        ctx.beginPath();
      }
      ctx.moveTo(fromNode.x, fromNode.y);
      ctx.lineTo(toNode.x, toNode.y);
      ctx.stroke();
      // Draw arrowhead for directed edges
      if (directed && color === "red") {
        ctx.fillStyle = ctx.strokeStyle;
        drawArrowhead(ctx, fromNode.x, fromNode.y, toNode.x, toNode.y, 16);
      }
      // Draw weight label for weighted edges
      if (weighted && edgeData.weight !== undefined && color === "red") {
        const mx = (fromNode.x + toNode.x) / 2;
        const my = (fromNode.y + toNode.y) / 2;
        ctx.fillStyle = "#fef9c3";
        ctx.font = "bold 12px system-ui, sans-serif";
        ctx.textAlign = "center";
        ctx.textBaseline = "middle";
        // Background pill for readability
        const label = String(edgeData.weight);
        const tw = ctx.measureText(label).width + 8;
        ctx.fillStyle = "rgba(15, 23, 42, 0.85)";
        ctx.beginPath();
        ctx.arc(mx, my, Math.max(tw / 2, 10), 0, Math.PI * 2);
        ctx.fill();
        ctx.fillStyle = "#fef9c3";
        ctx.fillText(label, mx, my);
      }
    });
    nodes.forEach((node, index) => {
      const radius = 16;
      const isSelected = node.id === selectedNodeId;
      const isSubSelected = subgraphMode && selectedSubVertices.has(node.id);
      if (isSubSelected) {
        ctx.save();
        ctx.strokeStyle = "rgba(253, 224, 71, 0.95)";
        ctx.lineWidth = 4;
        ctx.beginPath();
        ctx.arc(node.x, node.y, radius + 4, 0, Math.PI * 2);
        ctx.stroke();
        ctx.restore();
      }
      const gradient = ctx.createRadialGradient(
        node.x - 6,
        node.y - 6,
        4,
        node.x,
        node.y,
        radius + 2
      );
      gradient.addColorStop(0, isSelected ? "#a5b4fc" : "#34d399");
      gradient.addColorStop(1, isSelected ? "#6366f1" : "#10b981");
      ctx.fillStyle = gradient;
      ctx.beginPath();
      ctx.arc(node.x, node.y, radius, 0, Math.PI * 2);
      ctx.fill();
      ctx.lineWidth = 2;
      ctx.strokeStyle = isSelected ? "#fef9c3" : "rgba(255,255,255,0.6)";
      ctx.stroke();
      ctx.fillStyle = "#0b1224";
      ctx.font = "bold 13px system-ui, sans-serif";
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText(index.toString(), node.x, node.y);
    });
    // Marquee rectangle (Issue #11)
    if (marquee) {
      const x = Math.min(marquee.x0, marquee.x1);
      const y = Math.min(marquee.y0, marquee.y1);
      const w = Math.abs(marquee.x1 - marquee.x0);
      const h = Math.abs(marquee.y1 - marquee.y0);
      ctx.save();
      ctx.strokeStyle = "rgba(253, 224, 71, 0.9)";
      ctx.fillStyle = "rgba(253, 224, 71, 0.12)";
      ctx.lineWidth = 1;
      ctx.setLineDash([4, 4]);
      ctx.fillRect(x, y, w, h);
      ctx.strokeRect(x, y, w, h);
      ctx.restore();
    }
    ctx.restore();
  }, [nodes, edges, selectedNodeId, graphMode, directed, weighted,
      subgraphMode, selectedSubVertices, selectedSubEdges, marquee]);
  React.useEffect(() => {
    draw();
  }, [draw]);
  const findNodeAt = (x, y) => {
    const radius = 18;
    return nodes.find((node) => {
      const dx = node.x - x;
      const dy = node.y - y;
      return Math.hypot(dx, dy) <= radius;
    });
  };
  const findEdgeAt = (x, y) => {
    const tol = 6;
    let hit = null;
    edges.forEach((edgeData, key) => {
      if (edgeData.color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const na = nodes.find((n) => n.id === a);
      const nb = nodes.find((n) => n.id === b);
      if (!na || !nb) return;
      const vx = nb.x - na.x;
      const vy = nb.y - na.y;
      const len2 = vx * vx + vy * vy;
      if (len2 < 1) return;
      const t = Math.max(0, Math.min(1, ((x - na.x) * vx + (y - na.y) * vy) / len2));
      const px = na.x + t * vx;
      const py = na.y + t * vy;
      if (Math.hypot(px - x, py - y) <= tol) hit = key;
    });
    return hit;
  };
  const toggleSubVertex = (id, remove) => {
    setSelectedSubVertices((prev) => {
      const next = new Set(prev);
      if (remove) next.delete(id); else next.add(id);
      return next;
    });
  };
  const toggleSubEdge = (key, remove) => {
    setSelectedSubEdges((prev) => {
      const next = new Set(prev);
      if (remove) next.delete(key); else next.add(key);
      return next;
    });
  };
  const addNode = (x, y) => {
    pushHistory();
    const nextId = nodes.length > 0 ? Math.max(...nodes.map((n) => n.id)) + 1 : 0;
    const newNode = { id: nextId, x, y };
    setNodes((prev) => [...prev, newNode]);
    if (graphMode === "colored") {
      setEdges((prev) => {
        const newEdges = new Map(prev);
        for (const existing of nodes) {
          const key = sortedKey(existing.id, newNode.id);
          newEdges.set(key, { color: "blue" });
        }
        return newEdges;
      });
    }
    setStatus("Node added");
  };
  const toggleEdge = (aId, bId) => {
    if (aId === bId) return;
    pushHistory();
    const key = sortedKey(aId, bId);
    setEdges((prev) => {
      const newEdges = new Map(prev);
      const existing = newEdges.get(key);
      if (graphMode === "colored") {
        if (!existing || existing.color === "blue") {
          const edgeData = { color: "red" };
          if (directed) { edgeData.from = aId; edgeData.to = bId; }
          if (weighted) { edgeData.weight = existing && existing.weight ? existing.weight : nextWeight; }
          newEdges.set(key, edgeData);
          setStatus(`Edge ${key} set to red`);
        } else {
          const edgeData = { color: "blue" };
          newEdges.set(key, edgeData);
          setStatus(`Edge ${key} set to blue`);
        }
      } else {
        if (existing && existing.color === "red") {
          newEdges.delete(key);
          setStatus(`Edge ${key} removed`);
        } else {
          const edgeData = { color: "red" };
          if (directed) { edgeData.from = aId; edgeData.to = bId; }
          if (weighted) { edgeData.weight = nextWeight; }
          newEdges.set(key, edgeData);
          setStatus(`Edge ${key} added`);
        }
      }
      return newEdges;
    });
  };
  const deleteNode = (nodeId) => {
    pushHistory();
    setNodes((prev) => prev.filter((n) => n.id !== nodeId));
    setEdges((prev) => {
      const newEdges = new Map(prev);
      Array.from(newEdges.keys()).forEach((key) => {
        const [a, b] = key.split("-").map(Number);
        if (a === nodeId || b === nodeId) newEdges.delete(key);
      });
      return newEdges;
    });
    if (selectedNodeId === nodeId) setSelectedNodeId(null);
    setStatus(`Node ${nodeId} deleted`);
  };
  const canvasCoords = (e2) => {
    const canvas = canvasRef.current;
    if (!canvas) return null;
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    return { x: (e2.clientX - rect.left) * scaleX, y: (e2.clientY - rect.top) * scaleY, canvas };
  };
  const handleMouseDown = (e2) => {
    const c = canvasCoords(e2);
    if (!c) return;
    const { x, y } = c;
    const node = findNodeAt(x, y);
    // Subgraph mode: empty-space drag starts a marquee
    if (subgraphMode && e2.button !== 2 && !node) {
      setMarquee({ x0: x, y0: y, x1: x, y1: y });
      return;
    }
    if (e2.button === 2) {
      if (node && !subgraphMode) deleteNode(node.id);
      return;
    }
    if (node) {
      setDraggingNodeId(node.id);
      setDragOffset({ x: node.x - x, y: node.y - y });
      setDragStart({ x, y });
      setIsDragging(false);
      dragHistorySavedRef.current = false;
    }
  };
  const handleMouseMove = (e2) => {
    const c = canvasCoords(e2);
    if (!c) return;
    const { x, y, canvas } = c;
    if (marquee) {
      setMarquee((m) => m ? { ...m, x1: x, y1: y } : m);
      return;
    }
    if (draggingNodeId === null) return;
    if (subgraphMode) return; // don't drag-move nodes in subgraph mode
    const moved = Math.hypot(x - dragStart.x, y - dragStart.y) > 3;
    if (moved && !dragHistorySavedRef.current) {
      pushHistory();
      dragHistorySavedRef.current = true;
    }
    if (moved) setIsDragging(true);
    if (!isDragging && !moved) return;
    setNodes((prev) => prev.map((node) => {
      if (node.id === draggingNodeId) {
        return {
          ...node,
          x: clamp(x + dragOffset.x, 20, canvas.width - 20),
          y: clamp(y + dragOffset.y, 20, canvas.height - 20)
        };
      }
      return node;
    }));
  };
  const handleMouseUp = (e2) => {
    const c = canvasCoords(e2);
    if (!c) return;
    const { x, y } = c;
    // Finalize marquee selection (Issue #11)
    if (marquee) {
      const xMin = Math.min(marquee.x0, marquee.x1);
      const xMax = Math.max(marquee.x0, marquee.x1);
      const yMin = Math.min(marquee.y0, marquee.y1);
      const yMax = Math.max(marquee.y0, marquee.y1);
      const inside = new Set();
      nodes.forEach((node) => {
        if (node.x >= xMin && node.x <= xMax && node.y >= yMin && node.y <= yMax) {
          inside.add(node.id);
        }
      });
      if (inside.size > 0 || (xMax - xMin > 3 && yMax - yMin > 3)) {
        setSelectedSubVertices((prev) => {
          const next = new Set(prev);
          inside.forEach((id) => next.add(id));
          return next;
        });
        // Auto-include edges where both endpoints were dragged in together
        setSelectedSubEdges((prev) => {
          const next = new Set(prev);
          edges.forEach((edgeData, key) => {
            if (edgeData.color !== "red") return;
            const [a, b] = key.split("-").map(Number);
            if (inside.has(a) && inside.has(b)) next.add(key);
          });
          return next;
        });
        setStatus(`Marquee selected ${inside.size} vertices`);
      }
      setMarquee(null);
      setDraggingNodeId(null);
      return;
    }
    const node = findNodeAt(x, y);
    if (draggingNodeId !== null && isDragging) {
      setIsDragging(false);
      setDraggingNodeId(null);
      return;
    }
    // Subgraph mode click: add vertex/edge to selection (dblclick handles removal)
    if (subgraphMode) {
      if (node) {
        toggleSubVertex(node.id, false);
        setStatus(`Selected vertex ${node.id} for subgraph`);
      } else {
        const edgeKey = findEdgeAt(x, y);
        if (edgeKey) {
          toggleSubEdge(edgeKey, false);
          setStatus(`Selected edge ${edgeKey} for subgraph`);
        }
      }
      setDraggingNodeId(null);
      return;
    }
    if (node) {
      if (selectedNodeId === null) {
        setSelectedNodeId(node.id);
        setStatus(`Selected node ${node.id}`);
      } else {
        toggleEdge(selectedNodeId, node.id);
        setSelectedNodeId(null);
      }
    } else {
      addNode(x, y);
      setSelectedNodeId(null);
    }
    setIsDragging(false);
    setDraggingNodeId(null);
  };
  const handleDoubleClick = (e2) => {
    if (!subgraphMode) return;
    const c = canvasCoords(e2);
    if (!c) return;
    const { x, y } = c;
    const node = findNodeAt(x, y);
    if (node) {
      toggleSubVertex(node.id, true);
      setStatus(`Deselected vertex ${node.id}`);
      return;
    }
    const edgeKey = findEdgeAt(x, y);
    if (edgeKey) {
      toggleSubEdge(edgeKey, true);
      setStatus(`Deselected edge ${edgeKey}`);
    }
  };
  const handleContextMenu = (e2) => {
    e2.preventDefault();
  };
  const applyCircleLayout = () => {
    const n = nodes.length;
    if (n === 0) return;
    pushHistory();
    const radius = Math.min(canvasSize.width, canvasSize.height) / 2 - 40;
    const cx = canvasSize.width / 2;
    const cy = canvasSize.height / 2;
    setNodes((prev) => prev.map((node, i) => {
      const angle = 2 * Math.PI * i / n;
      return {
        ...node,
        x: cx + radius * Math.cos(angle),
        y: cy + radius * Math.sin(angle)
      };
    }));
    setStatus("Applied circle layout");
  };
  const applySpringLayout = () => {
    const n = nodes.length;
    if (n === 0) return;
    pushHistory();
    const area = canvasSize.width * canvasSize.height;
    const k = Math.sqrt(area / (n + 1e-3));
    let temperature = Math.min(canvasSize.width, canvasSize.height) / 8;
    const iterations = 250;
    let currentNodes = [...nodes];
    const idToIndex = new Map(currentNodes.map((node, i) => [node.id, i]));
    for (let iter = 0; iter < iterations; iter++) {
      const disp = currentNodes.map(() => ({ x: 0, y: 0 }));
      for (let i = 0; i < n; i++) {
        for (let j = i + 1; j < n; j++) {
          const dx = currentNodes[j].x - currentNodes[i].x;
          const dy = currentNodes[j].y - currentNodes[i].y;
          const dist = Math.hypot(dx, dy) + 0.01;
          const force = k * k / dist;
          const fx = force * dx / dist;
          const fy = force * dy / dist;
          disp[i].x -= fx;
          disp[i].y -= fy;
          disp[j].x += fx;
          disp[j].y += fy;
        }
      }
      edges.forEach(({ color }, key) => {
        if (color !== "red") return;
        const [aId, bId] = key.split("-").map(Number);
        const i = idToIndex.get(aId);
        const j = idToIndex.get(bId);
        if (i === void 0 || j === void 0) return;
        const dx = currentNodes[j].x - currentNodes[i].x;
        const dy = currentNodes[j].y - currentNodes[i].y;
        const dist = Math.hypot(dx, dy) + 0.01;
        const force = dist * dist / k;
        const fx = force * dx / dist;
        const fy = force * dy / dist;
        disp[i].x += fx;
        disp[i].y += fy;
        disp[j].x -= fx;
        disp[j].y -= fy;
      });
      for (let i = 0; i < n; i++) {
        const dx = disp[i].x;
        const dy = disp[i].y;
        const dist = Math.hypot(dx, dy) || 1;
        const limited = Math.min(temperature, dist);
        currentNodes[i].x = clamp(
          currentNodes[i].x + dx / dist * limited,
          20,
          canvasSize.width - 20
        );
        currentNodes[i].y = clamp(
          currentNodes[i].y + dy / dist * limited,
          20,
          canvasSize.height - 20
        );
      }
      temperature *= 0.95;
      if (temperature < 0.5) break;
    }
    setNodes(currentNodes);
    setStatus("Applied force-directed layout");
  };
  const clearGraph = () => {
    pushHistory();
    setNodes([]);
    setEdges(/* @__PURE__ */ new Map());
    setSelectedNodeId(null);
    setStatus("Graph cleared");
  };
  // Issue #1 fix: ensureCompleteGraph / stripBlueEdges on mode switch
  const switchGraphMode = (newMode) => {
    pushHistory();
    if (newMode === "colored") {
      setEdges((prev) => {
        const newEdges = new Map(prev);
        for (let i = 0; i < nodes.length; i++) {
          for (let j = i + 1; j < nodes.length; j++) {
            const key = sortedKey(nodes[i].id, nodes[j].id);
            if (!newEdges.has(key)) {
              newEdges.set(key, { color: "blue" });
            }
          }
        }
        return newEdges;
      });
      setStatus("Bi-colored mode: complete graph; toggle red/blue");
    } else {
      setEdges((prev) => {
        const newEdges = new Map();
        prev.forEach((val, key) => {
          if (val.color === "red") newEdges.set(key, val);
        });
        return newEdges;
      });
      setStatus("Simple mode: add/remove edges");
    }
    setGraphMode(newMode);
  };
  const buildAdjMatrixArray = () => {
    const n = nodes.length;
    const idToIndex = new Map(nodes.map((n2, i) => [n2.id, i]));
    const matrix = Array.from({ length: n }, () => Array(n).fill(0));
    edges.forEach((edgeData, key) => {
      if (edgeData.color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const val = weighted && edgeData.weight !== undefined ? edgeData.weight : 1;
      if (directed && edgeData.from !== undefined) {
        const fi = idToIndex.get(edgeData.from);
        const ti = idToIndex.get(edgeData.to);
        if (fi !== void 0 && ti !== void 0) matrix[fi][ti] = val;
      } else {
        const i = idToIndex.get(a);
        const j = idToIndex.get(b);
        if (i !== void 0 && j !== void 0) {
          matrix[i][j] = val;
          matrix[j][i] = val;
        }
      }
    });
    return matrix;
  };
  // Issue #10/#11: send payload matches widget mode.
  //   simple + !directed + !weighted  →  kind="g6",       send graph6 string
  //   directed (any)                   →  kind="directed", send adjacency matrix
  //   weighted (any, non-directed)     →  kind="weighted", send weight matrix
  //   subgraph mode with any selection →  kind="subgraph", send matrix + selected v/e
  const sendToLean = () => {
    setStatus("Sending to Lean...");
    const idToIndex = new Map(nodes.map((n2, i) => [n2.id, i]));
    const hasSelection = selectedSubVertices.size > 0 || selectedSubEdges.size > 0;
    let kind = "g6";
    if (subgraphMode && hasSelection) kind = "subgraph";
    else if (directed) kind = "directed";
    else if (weighted) kind = "weighted";
    const matrix = kind === "g6" ? [] : buildAdjMatrixArray();
    const selectedVertices = [];
    const selectedEdges = [];
    if (kind === "subgraph") {
      selectedSubVertices.forEach((id) => {
        const idx = idToIndex.get(id);
        if (idx !== void 0) selectedVertices.push(idx);
      });
      selectedSubEdges.forEach((key) => {
        const [a, b] = key.split("-").map(Number);
        const ia = idToIndex.get(a);
        const ib = idToIndex.get(b);
        if (ia === void 0 || ib === void 0) return;
        const edgeData = edges.get(key);
        if (directed && edgeData && edgeData.from !== undefined) {
          const fi = idToIndex.get(edgeData.from);
          const ti = idToIndex.get(edgeData.to);
          if (fi !== void 0 && ti !== void 0) selectedEdges.push([fi, ti]);
        } else {
          selectedEdges.push([ia, ib]);
        }
      });
      selectedVertices.sort((a, b) => a - b);
    }
    rs.call("graphWidget.sendGraph", {
      kind,
      graph6: graph6String,
      matrix,
      selectedVertices,
      selectedEdges,
      replaceRange: range
    }).then((result) => {
      if (result.edit) {
        ec.api.applyEdit({ documentChanges: [result.edit] });
      }
      if (result.newSelection) {
        ec.revealLocation({
          uri: result.edit.textDocument.uri,
          range: result.newSelection
        });
      }
      setStatus(`Graph sent to Lean (${kind})`);
    }).catch((e2) => {
      console.error(mapRpcError(e2));
      setStatus("Error sending to Lean");
    });
  };
  const exportEdgeList = () => {
    if (nodes.length === 0) return "";
    const idToIndex = new Map(nodes.map((n, i) => [n.id, i]));
    const lines = [];
    edges.forEach((edgeData, key) => {
      if (edgeData.color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const ia = idToIndex.get(a);
      const ib = idToIndex.get(b);
      if (ia !== void 0 && ib !== void 0) {
        if (directed && edgeData.from !== undefined) {
          const ifrom = idToIndex.get(edgeData.from);
          const ito = idToIndex.get(edgeData.to);
          const w = weighted && edgeData.weight !== undefined ? ` ${edgeData.weight}` : "";
          lines.push(`${ifrom} ${ito}${w}`);
        } else {
          const w = weighted && edgeData.weight !== undefined ? ` ${edgeData.weight}` : "";
          lines.push(`${ia} ${ib}${w}`);
        }
      }
    });
    return lines.join("\n");
  };
  const exportAdjMatrix = () => {
    const n = nodes.length;
    const idToIndex = new Map(nodes.map((n2, i) => [n2.id, i]));
    const useWeights = weighted;
    const matrix = Array.from({ length: n }, () => Array(n).fill(0));
    edges.forEach((edgeData, key) => {
      if (edgeData.color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const i = idToIndex.get(a);
      const j = idToIndex.get(b);
      if (i !== void 0 && j !== void 0) {
        const val = useWeights && edgeData.weight !== undefined ? edgeData.weight : 1;
        if (directed && edgeData.from !== undefined) {
          const fi = idToIndex.get(edgeData.from);
          const ti = idToIndex.get(edgeData.to);
          if (fi !== void 0 && ti !== void 0) matrix[fi][ti] = val;
        } else {
          matrix[i][j] = val;
          matrix[j][i] = val;
        }
      }
    });
    return matrix.map((row) => row.join(" ")).join("\n");
  };
  return e("div", { style: {
    fontFamily: "system-ui, sans-serif",
    background: "#0f172a",
    color: "#e2e8f0",
    borderRadius: "8px",
    overflow: "hidden"
  } }, [
    // Header
    e("div", { style: {
      padding: "12px 16px",
      background: "rgba(15, 23, 42, 0.75)",
      borderBottom: "1px solid rgba(255, 255, 255, 0.08)"
    } }, [
      e("h3", { style: { margin: "0 0 8px 0", fontSize: "16px" } }, "Graph Widget"),
      e("div", { style: { display: "flex", gap: "8px", flexWrap: "wrap", alignItems: "center" } }, [
        e("span", { style: {
          padding: "4px 8px",
          background: "rgba(255, 255, 255, 0.08)",
          borderRadius: "999px",
          fontSize: "12px",
          border: "1px solid rgba(255, 255, 255, 0.15)"
        } }, `Nodes: ${nodes.length}`),
        e("span", { style: {
          padding: "4px 8px",
          background: "rgba(255, 255, 255, 0.08)",
          borderRadius: "999px",
          fontSize: "12px",
          border: "1px solid rgba(255, 255, 255, 0.15)"
        } }, `Edges: ${edgeCount}`),
        e("button", {
          onClick: () => setSelectedNodeId(null),
          style: btnStyle
        }, "Clear selection"),
        e("button", {
          onClick: clearGraph,
          style: {
            border: "1px solid rgba(239, 68, 68, 0.35)",
            background: "rgba(239, 68, 68, 0.15)",
            color: "#fecdd3",
            padding: "6px 10px",
            borderRadius: "6px",
            cursor: "pointer",
            fontSize: "12px"
          }
        }, "Clear graph"),
        // Undo button (Issue #4)
        e("button", {
          onClick: undo,
          style: btnStyle
        }, "Undo (Ctrl+Z)"),
        e("select", {
          value: graphMode,
          onChange: (ev) => switchGraphMode(ev.target.value),
          style: {
            border: "1px solid rgba(255, 255, 255, 0.15)",
            background: "rgba(255, 255, 255, 0.08)",
            color: "inherit",
            padding: "6px 10px",
            borderRadius: "6px",
            fontSize: "12px",
            cursor: "pointer"
          }
        }, [
          e("option", { value: "simple" }, "Simple graph"),
          e("option", { value: "colored" }, "Bi-colored graph")
        ]),
        // Directed toggle (Issue #3)
        e("label", { style: { fontSize: "12px", display: "flex", alignItems: "center", gap: "4px", cursor: "pointer" } }, [
          e("input", {
            type: "checkbox",
            checked: directed,
            onChange: (ev) => setDirected(ev.target.checked)
          }),
          "Directed"
        ]),
        // Weighted toggle (Issue #3)
        e("label", { style: { fontSize: "12px", display: "flex", alignItems: "center", gap: "4px", cursor: "pointer" } }, [
          e("input", {
            type: "checkbox",
            checked: weighted,
            onChange: (ev) => setWeighted(ev.target.checked)
          }),
          "Weighted"
        ]),
        weighted ? e("label", { style: { fontSize: "12px", display: "flex", alignItems: "center", gap: "4px" } }, [
          "W:",
          e("input", {
            type: "number",
            value: nextWeight,
            onChange: (ev) => setNextWeight(Number(ev.target.value) || 1),
            style: {
              width: "50px",
              border: "1px solid rgba(255, 255, 255, 0.15)",
              background: "rgba(255, 255, 255, 0.08)",
              color: "inherit",
              padding: "4px 6px",
              borderRadius: "4px",
              fontSize: "12px"
            }
          })
        ]) : null,
        e("button", {
          onClick: applyCircleLayout,
          style: btnStyle
        }, "Circle layout"),
        e("button", {
          onClick: applySpringLayout,
          style: btnStyle
        }, "Spring layout"),
        // Highlight subgraph toggle (Issue #11)
        e("button", {
          onClick: () => {
            const next = !subgraphMode;
            setSubgraphMode(next);
            if (!next) {
              setSelectedSubVertices(new Set());
              setSelectedSubEdges(new Set());
              setMarquee(null);
            }
            setStatus(next ? "Subgraph mode: drag / click to select, double-click to deselect" : "Subgraph mode off");
          },
          style: subgraphMode ? {
            ...btnStyle,
            background: "rgba(253, 224, 71, 0.18)",
            borderColor: "rgba(253, 224, 71, 0.55)",
            color: "#fef9c3"
          } : btnStyle
        }, subgraphMode ? "Exit subgraph mode" : "Highlight subgraph"),
        subgraphMode ? e("span", { style: {
          padding: "4px 8px",
          background: "rgba(253, 224, 71, 0.1)",
          borderRadius: "999px",
          fontSize: "12px",
          border: "1px solid rgba(253, 224, 71, 0.3)",
          color: "#fef9c3"
        } }, `Sub: ${selectedSubVertices.size}v / ${selectedSubEdges.size}e`) : null
      ])
    ]),
    // Canvas
    e("canvas", {
      ref: canvasRef,
      width: canvasSize.width,
      height: canvasSize.height,
      onMouseDown: handleMouseDown,
      onMouseMove: handleMouseMove,
      onMouseUp: handleMouseUp,
      onDoubleClick: handleDoubleClick,
      onContextMenu: handleContextMenu,
      style: {
        display: "block",
        width: "100%",
        background: "radial-gradient(circle at 50% 50%, rgba(255, 255, 255, 0.04), transparent 60%), #0b1224",
        cursor: subgraphMode ? "cell" : "crosshair"
      }
    }),
    // Bottom panel
    e("div", { style: {
      padding: "12px 16px",
      background: "rgba(10, 14, 26, 0.85)",
      borderTop: "1px solid rgba(255, 255, 255, 0.08)"
    } }, [
      e("div", { style: {
        fontSize: "11px",
        color: "#cbd5e1",
        marginBottom: "8px"
      } }, "Click empty space to add a node. Click two nodes to toggle edge. Drag to reposition. Right-click to delete. Ctrl+Z to undo."),
      e("div", { style: { display: "flex", gap: "8px", marginBottom: "8px", flexWrap: "wrap" } }, [
        e("button", {
          onClick: sendToLean,
          style: {
            background: "linear-gradient(135deg, #22d3ee, #6366f1)",
            color: "#0b1224",
            border: "none",
            padding: "8px 16px",
            borderRadius: "6px",
            cursor: "pointer",
            fontWeight: "600",
            fontSize: "13px"
          }
        }, "\u{1F4E4} Send to Lean"),
        // Issue #10: hide Copy graph6 when directed/weighted — g6 doesn't encode those
        (!directed && !weighted) ? e("button", {
          onClick: () => {
            navigator.clipboard.writeText(graph6String);
            setStatus("Copied graph6 to clipboard");
          },
          style: btnStyle
        }, "Copy graph6") : null,
        e("button", {
          onClick: () => {
            navigator.clipboard.writeText(exportEdgeList());
            setStatus("Copied edge list to clipboard");
          },
          style: btnStyle
        }, "Copy edges"),
        e("button", {
          onClick: () => {
            navigator.clipboard.writeText(exportAdjMatrix());
            setStatus("Copied adjacency matrix to clipboard");
          },
          style: btnStyle
        }, "Copy matrix")
      ]),
      (!directed && !weighted) ? e("div", { style: {
        fontSize: "11px",
        fontFamily: "monospace",
        color: "#94a3b8",
        wordBreak: "break-all",
        marginBottom: "4px"
      } }, `graph6: ${graph6String}`) : null,
      e("div", { style: {
        fontSize: "11px",
        color: "#cbd5e1",
        fontStyle: "italic"
      } }, status)
    ])
  ]);
}
export {
  widget_graph_default as default
};
