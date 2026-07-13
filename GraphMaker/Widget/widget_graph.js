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
  border: "1px solid rgba(255, 255, 255, 0.12)",
  background: "rgba(255, 255, 255, 0.06)",
  backdropFilter: "blur(8px)",
  WebkitBackdropFilter: "blur(8px)",
  color: "#e2e8f0",
  padding: "7px 12px",
  borderRadius: "8px",
  cursor: "pointer",
  fontSize: "11px",
  fontWeight: "500",
  letterSpacing: "0.01em",
  transition: "all 0.2s ease"
};

// Pure layout: returns repositioned nodes for a given layout name.
// (The interactive apply*Layout functions wrap this with setNodes/pushHistory.)
function layoutNodes(nodes, edges, name, W = 600, H = 400) {
  const n = nodes.length;
  if (n === 0 || !name) return nodes;
  const cx = W / 2, cy = H / 2;
  const R = Math.min(W, H) / 2 - 40;
  if (name === "circle") {
    return nodes.map((nd, i) => {
      const a = 2 * Math.PI * i / n;
      return { ...nd, x: cx + R * Math.cos(a), y: cy + R * Math.sin(a) };
    });
  }
  if (name === "concentric") {
    const outer = Math.ceil(n / 2);
    return nodes.map((nd, i) => {
      if (i < outer) {
        const a = 2 * Math.PI * i / outer - Math.PI / 2;
        return { ...nd, x: cx + R * Math.cos(a), y: cy + R * Math.sin(a) };
      }
      const k = i - outer, inner = n - outer;
      const a = 2 * Math.PI * k / inner - Math.PI / 2;
      return { ...nd, x: cx + R * 0.5 * Math.cos(a), y: cy + R * 0.5 * Math.sin(a) };
    });
  }
  if (name === "hub") {
    const degree = (id) => {
      let d = 0;
      edges.forEach((e, key) => {
        if (e.color !== "red") return;
        const [a, b] = key.split("-").map(Number);
        if (a === id || b === id) d++;
      });
      return d;
    };
    let hubId = nodes[0].id, hubDeg = -1;
    for (const nd of nodes) { const d = degree(nd.id); if (d > hubDeg) { hubDeg = d; hubId = nd.id; } }
    const rim = nodes.filter((nd) => nd.id !== hubId);
    return nodes.map((nd) => {
      if (nd.id === hubId) return { ...nd, x: cx, y: cy };
      const k = rim.findIndex((r) => r.id === nd.id);
      const a = 2 * Math.PI * k / rim.length - Math.PI / 2;
      return { ...nd, x: cx + R * Math.cos(a), y: cy + R * Math.sin(a) };
    });
  }
  if (name === "cube") {
    const d = Math.round(Math.log2(n));
    if (2 ** d !== n) return layoutNodes(nodes, edges, "concentric", W, H);
    const basis = [{ x: 1, y: 0 }, { x: 0, y: 1 }, { x: 0.45, y: 0.45 }, { x: 0.45, y: -0.45 }];
    let maxExt = 0;
    for (let bit = 0; bit < d; bit++) maxExt += Math.abs((basis[bit] || {}).x || 0);
    return nodes.map((nd, i) => {
      let x = 0, y = 0;
      for (let bit = 0; bit < d; bit++) {
        const set = (i >> bit) & 1 ? 1 : -1;
        const b = basis[bit] || { x: 0, y: 0 };
        x += set * b.x; y += set * b.y;
      }
      const norm = Math.max(1, maxExt);
      return { ...nd, x: cx + (x / norm) * R * 0.9, y: cy + (y / norm) * R * 0.9 };
    });
  }
  return nodes;  // spring / unknown → leave as-is (handled interactively)
}

function initFromMatrix(matrix, canvasWidth, canvasHeight, isDirected, bicolored) {
  const n = matrix.length;
  if (n === 0) return { nodes: [], edges: new Map() };
  const nodes = [];
  const radius = Math.min(canvasWidth, canvasHeight) / 2 - 40;
  const cx = canvasWidth / 2;
  const cy = canvasHeight / 2;
  for (let i = 0; i < n; i++) {
    const angle = 2 * Math.PI * i / n;
    nodes.push({ id: i, x: cx + radius * Math.cos(angle), y: cy + radius * Math.sin(angle) });
  }
  const edges = new Map();
  if (isDirected) {
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (i === j || matrix[i][j] === 0) continue;
        const key = sortedKey(i, j);
        if (!edges.has(key)) {
          edges.set(key, { color: "red", from: i, to: j, weight: matrix[i][j] });
        }
      }
    }
  } else {
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        const key = sortedKey(i, j);
        if (matrix[i][j] !== 0) {
          edges.set(key, { color: "red", weight: matrix[i][j] });
        } else if (bicolored) {
          edges.set(key, { color: "blue" });
        }
      }
    }
  }
  return { nodes, edges };
}

function widget_graph_default(props) {
  const rs = React.useContext(RpcContext);
  const ec = React.useContext(EditorContext);
  const canvasRef = React.useRef(null);
  const [canvasSize, setCanvasSize] = React.useState({ width: 600, height: 400 });
  const [zoom, setZoom] = React.useState(1);
  const [pan, setPan] = React.useState({ x: 0, y: 0 });
  const readOnly = props.readOnly || false;
  const initMatrix = props.initialMatrix || [];
  const initialGraph = initMatrix.length > 0
    ? initFromMatrix(initMatrix, canvasSize.width, canvasSize.height, props.directed || false, false)
    : parseGraph6(props.graph6 || "?", canvasSize.width, canvasSize.height);
  const [nodes, setNodes] = React.useState(initialGraph.nodes);
  const [edges, setEdges] = React.useState(initialGraph.edges);
  const [status, setStatus] = React.useState(readOnly ? "View only" : "Ready");
  const [range, _] = React.useState(props.replaceRange);
  const [graphMode, setGraphMode] = React.useState("simple");
  const [directed, setDirected] = React.useState(props.directed || false);
  const [weighted, setWeighted] = React.useState(props.weighted || false);
  const [nextWeight, setNextWeight] = React.useState(1);
  const [selectedNodeId, setSelectedNodeId] = React.useState(null);
  const [draggingNodeId, setDraggingNodeId] = React.useState(null);
  const [dragOffset, setDragOffset] = React.useState({ x: 0, y: 0 });
  const [dragStart, setDragStart] = React.useState({ x: 0, y: 0 });
  const [isDragging, setIsDragging] = React.useState(false);
  const dragHistorySavedRef = React.useRef(false);
  const [showLabels, setShowLabels] = React.useState(false);
  const [selectedEdgeId, setSelectedEdgeId] = React.useState(null);
  const edgeTypingRef = React.useRef(false);
  const prevSelectedEdgeRef = React.useRef(null);

  // When edge is deselected, check if weight is 0 and auto-delete
  React.useEffect(() => {
    const prevKey = prevSelectedEdgeRef.current;
    if (prevKey && prevKey !== selectedEdgeId) {
      const edge = edges.get(prevKey);
      if (edge && edge.weight === 0) {
        setEdges((prev) => {
          const newEdges = new Map(prev);
          newEdges.delete(prevKey);
          return newEdges;
        });
      }
    }
    prevSelectedEdgeRef.current = selectedEdgeId;
  });

  // Selection mode: "none", "subgraph", "walk"
  const [selectMode, setSelectMode] = React.useState("none");
  const [selectedEdges, setSelectedEdges] = React.useState(new Set());
  const [selectedVerts, setSelectedVerts] = React.useState(new Set());
  // Walk mode: ordered list of vertex ids forming the path
  const [walkPath, setWalkPath] = React.useState([]);

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

  // Keyboard handler: Ctrl+Z undo, Delete/Backspace to delete selected node
  React.useEffect(() => {
    const handler = (ev) => {
      if ((ev.ctrlKey || ev.metaKey) && ev.key === "z") {
        ev.preventDefault();
        if (selectMode === "walk" && walkPath.length > 0) {
          setWalkPath((prev) => prev.slice(0, -1));
          setStatus("Walk: undone last vertex");
        } else if (selectMode === "subgraph" && (selectedEdges.size > 0 || selectedVerts.size > 0)) {
          setSelectedEdges(new Set());
          setSelectedVerts(new Set());
          setStatus("Subgraph selection cleared");
        } else {
          undo();
        }
      }
      if (ev.key === "Delete") {
        if (selectedNodeId !== null) {
          ev.preventDefault();
          deleteNode(selectedNodeId);
        } else if (selectedEdgeId !== null) {
          ev.preventDefault();
          pushHistory();
          setEdges((prev) => {
            const newEdges = new Map(prev);
            newEdges.delete(selectedEdgeId);
            return newEdges;
          });
          setStatus(`Edge ${selectedEdgeId} deleted`);
          setSelectedEdgeId(null);
        }
      }
      // Type digits to change weight of selected edge (first key replaces, then appends)
      if (selectedEdgeId !== null && /^[0-9]$/.test(ev.key)) {
        ev.preventDefault();
        const newStr = edgeTypingRef.current
          ? String((edges.get(selectedEdgeId) || {}).weight || "") + ev.key
          : ev.key;
        const newWeight = Number(newStr);
        edgeTypingRef.current = true;
        pushHistory();
        setEdges((prev) => {
          const newEdges = new Map(prev);
          const e = prev.get(selectedEdgeId);
          newEdges.set(selectedEdgeId, { ...e, weight: newWeight });
          return newEdges;
        });
        if (!weighted) setWeighted(true);
        setStatus(`Edge ${selectedEdgeId} weight: ${newWeight}`);
      }
      // Backspace: trim last digit of selected edge weight, or delete selected node
      if (ev.key === "Backspace") {
        if (selectedEdgeId !== null) {
          ev.preventDefault();
          const edge = edges.get(selectedEdgeId);
          const currentStr = edge && edge.weight !== undefined ? String(edge.weight) : "";
          const newStr = currentStr.slice(0, -1);
          const newWeight = newStr.length > 0 ? Number(newStr) : 0;
          pushHistory();
          setEdges((prev) => {
            const newEdges = new Map(prev);
            const e = prev.get(selectedEdgeId);
            newEdges.set(selectedEdgeId, { ...e, weight: newWeight });
            return newEdges;
          });
          setStatus(`Edge ${selectedEdgeId} weight: ${newWeight}`);
        } else if (selectedNodeId !== null) {
          ev.preventDefault();
          deleteNode(selectedNodeId);
        }
      }
      // Enter deselects edge
      if (ev.key === "Enter" && selectedEdgeId !== null) {
        ev.preventDefault();
        setSelectedEdgeId(null);
        edgeTypingRef.current = false;
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
    const dpr = window.devicePixelRatio || 1;
    canvas.width = canvasSize.width * dpr;
    canvas.height = canvasSize.height * dpr;
    const ctx = canvas.getContext("2d");
    if (!ctx) return;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, canvasSize.width, canvasSize.height);
    ctx.save();
    // Apply zoom + pan
    const cx = canvasSize.width / 2;
    const cy = canvasSize.height / 2;
    ctx.translate(cx + pan.x, cy + pan.y);
    ctx.scale(zoom, zoom);
    ctx.translate(-cx, -cy);
    ctx.lineWidth = 2;
    edges.forEach((edgeData, key) => {
      const { color } = edgeData;
      if (graphMode === "simple" && color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const na = nodes.find((n) => n.id === a);
      const nb = nodes.find((n) => n.id === b);
      if (!na || !nb) return;
      const isSubgraphEdge = selectMode === "subgraph" && selectedEdges.has(key);
      const isWalkEdge = selectMode === "walk" && walkPath.length >= 2 && (() => {
        for (let idx = 0; idx < walkPath.length - 1; idx++) {
          const wKey = directed ? sortedKey(walkPath[idx], walkPath[idx + 1]) : sortedKey(walkPath[idx], walkPath[idx + 1]);
          if (wKey === key) return true;
        }
        return false;
      })();
      const isSelectedEdge = isSubgraphEdge || isWalkEdge || selectedEdgeId === key;
      ctx.strokeStyle = isWalkEdge ? "rgba(34, 197, 94, 0.95)"
        : isSelectedEdge ? "rgba(250, 204, 21, 0.95)"
        : color === "blue" ? "rgba(96, 165, 250, 0.85)" : "rgba(248, 113, 113, 0.9)";
      ctx.lineWidth = isSelectedEdge ? 4 : 2;
      ctx.beginPath();
      // For directed edges, determine source/target
      let fromNode = na;
      let toNode = nb;
      if (directed && edgeData.from !== undefined) {
        fromNode = nodes.find((n) => n.id === edgeData.from) || na;
        toNode = nodes.find((n) => n.id === edgeData.to) || nb;
      }
      ctx.moveTo(fromNode.x, fromNode.y);
      ctx.lineTo(toNode.x, toNode.y);
      ctx.stroke();
      // Draw arrowhead for directed edges
      if (directed && color === "red") {
        ctx.fillStyle = ctx.strokeStyle;
        drawArrowhead(ctx, fromNode.x, fromNode.y, toNode.x, toNode.y, 22);
      }
      // Draw weight label for weighted edges
      if (weighted && edgeData.weight !== undefined && color === "red") {
        const mx = (fromNode.x + toNode.x) / 2;
        const my = (fromNode.y + toNode.y) / 2;
        const isEdgeSelected = selectedEdgeId === key;
        ctx.font = "bold 12px system-ui, sans-serif";
        ctx.textAlign = "center";
        ctx.textBaseline = "middle";
        const label = String(edgeData.weight);
        const tw = ctx.measureText(label).width + 8;
        // Background pill — highlighted yellow when selected
        ctx.fillStyle = isEdgeSelected ? "rgba(250, 204, 21, 0.95)" : "rgba(15, 23, 42, 0.85)";
        ctx.beginPath();
        ctx.arc(mx, my, Math.max(tw / 2, 10), 0, Math.PI * 2);
        ctx.fill();
        ctx.fillStyle = isEdgeSelected ? "#0b1224" : "#fef9c3";
        ctx.fillText(label, mx, my);
      }
    });
    nodes.forEach((node, index) => {
      const radius = 22;
      const isSelected = node.id === selectedNodeId;
      const isSubgraphVert = (selectMode === "subgraph" && selectedVerts.has(node.id)) ||
        (selectMode === "walk" && walkPath.includes(node.id));
      const gradient = ctx.createRadialGradient(
        node.x - 6,
        node.y - 6,
        4,
        node.x,
        node.y,
        radius + 2
      );
      gradient.addColorStop(0, isSubgraphVert ? "#fde047" : isSelected ? "#a5b4fc" : "#34d399");
      gradient.addColorStop(1, isSubgraphVert ? "#ca8a04" : isSelected ? "#6366f1" : "#10b981");
      ctx.fillStyle = gradient;
      ctx.beginPath();
      ctx.arc(node.x, node.y, radius, 0, Math.PI * 2);
      ctx.fill();
      ctx.lineWidth = isSubgraphVert ? 3 : 2;
      ctx.strokeStyle = isSubgraphVert ? "#fef9c3" : isSelected ? "#fef9c3" : "rgba(255,255,255,0.6)";
      ctx.stroke();
      if (showLabels) {
        ctx.fillStyle = "#0b1224";
        ctx.font = "bold 13px system-ui, sans-serif";
        ctx.textAlign = "center";
        ctx.textBaseline = "middle";
        ctx.fillText(index.toString(), node.x, node.y);
      }
    });
    ctx.restore();
  }, [nodes, edges, selectedNodeId, selectedEdgeId, graphMode, directed, weighted, canvasSize, selectMode, selectedEdges, selectedVerts, walkPath, zoom, pan, showLabels]);
  React.useEffect(() => {
    draw();
  }, [draw]);
  // Re-initialize when the incoming graph changes (e.g. cursor moves between two
  // `draw_graph` calls). React reuses the component instance, so `useState` initial
  // values are stale — reset explicitly on a new matrix/graph6 signature.
  const initSig = JSON.stringify(initMatrix) + "|" + (props.graph6 || "") + "|" +
    (props.directed ? "d" : "") + (props.weighted ? "w" : "");
  const prevInitSig = React.useRef(initSig);
  const didInitLayout = React.useRef(false);
  React.useEffect(() => {
    if (prevInitSig.current !== initSig) {
      prevInitSig.current = initSig;
      const g = initMatrix.length > 0
        ? initFromMatrix(initMatrix, canvasSize.width, canvasSize.height, props.directed || false, false)
        : parseGraph6(props.graph6 || "?", canvasSize.width, canvasSize.height);
      // Apply the default layout to the fresh nodes before committing state.
      setNodes(layoutNodes(g.nodes, g.edges, props.layout, canvasSize.width, canvasSize.height));
      setEdges(g.edges);
      setDirected(props.directed || false);
      setWeighted(props.weighted || false);
      setSelectedNodeId(null);
      setSelectedEdgeId(null);
      setSelectMode("none");
      setWalkPath([]);
      setZoom(1);
      setPan({ x: 0, y: 0 });
      didInitLayout.current = true;
    }
  }, [initSig]);
  // Apply the default layout once on the very first mount.
  React.useEffect(() => {
    if (!didInitLayout.current && props.layout && nodes.length > 0) {
      didInitLayout.current = true;
      setNodes((prev) => layoutNodes(prev, edges, props.layout, canvasSize.width, canvasSize.height));
    }
  }, [nodes.length]);
  const screenToWorld = (sx, sy) => {
    const cx = canvasSize.width / 2;
    const cy = canvasSize.height / 2;
    return {
      x: (sx - cx - pan.x) / zoom + cx,
      y: (sy - cy - pan.y) / zoom + cy
    };
  };
  const findNodeAt = (x, y) => {
    let closest = null;
    let closestDist = Infinity;
    const maxRadius = 28;
    for (const node of nodes) {
      const dist = Math.hypot(node.x - x, node.y - y);
      if (dist <= maxRadius && dist < closestDist) {
        closest = node;
        closestDist = dist;
      }
    }
    return closest;
  };
  const findEdgeAt = (x, y) => {
    const threshold = 30;
    let closest = null;
    let closestDist = Infinity;
    edges.forEach((edgeData, key) => {
      if (edgeData.color !== "red") return;
      const [aId, bId] = key.split("-").map(Number);
      const na = nodes.find((n) => n.id === aId);
      const nb = nodes.find((n) => n.id === bId);
      if (!na || !nb) return;
      // Point-to-segment distance
      const dx = nb.x - na.x;
      const dy = nb.y - na.y;
      const lenSq = dx * dx + dy * dy;
      if (lenSq === 0) return;
      let t = ((x - na.x) * dx + (y - na.y) * dy) / lenSq;
      t = Math.max(0, Math.min(1, t));
      const px = na.x + t * dx;
      const py = na.y + t * dy;
      const dist = Math.hypot(x - px, y - py);
      if (dist < threshold && dist < closestDist) {
        closestDist = dist;
        closest = key;
      }
    });
    return closest;
  };
  const addNode = (x, y) => {
    pushHistory();
    setNodes((prev) => {
      // Don't create nodes too close to existing ones (2 * visual radius)
      for (const node of prev) {
        if (Math.hypot(node.x - x, node.y - y) < 44) return prev;
      }
      const nextId = prev.length > 0 ? Math.max(...prev.map((n) => n.id)) + 1 : 0;
      return [...prev, { id: nextId, x, y }];
    });
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
  const handleMouseDown = (e2) => {
    if (readOnly) return;
    const canvas = canvasRef.current;
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvasSize.width / rect.width;
    const scaleY = canvasSize.height / rect.height;
    const sx = (e2.clientX - rect.left) * scaleX;
    const sy = (e2.clientY - rect.top) * scaleY;
    const { x, y } = screenToWorld(sx, sy);
    const node = findNodeAt(x, y);
    if (e2.button === 2) {
      if (node) deleteNode(node.id);
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
    if (draggingNodeId === null) return;
    const canvas = canvasRef.current;
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvasSize.width / rect.width;
    const scaleY = canvasSize.height / rect.height;
    const sx = (e2.clientX - rect.left) * scaleX;
    const sy = (e2.clientY - rect.top) * scaleY;
    const { x, y } = screenToWorld(sx, sy);
    const moved = Math.hypot(x - dragStart.x, y - dragStart.y) > 3;
    if (moved && !dragHistorySavedRef.current) {
      pushHistory();
      dragHistorySavedRef.current = true;
    }
    if (moved) setIsDragging(true);
    if (!isDragging && !moved) return;
    setNodes((prev) => prev.map((node) => {
      if (node.id === draggingNodeId) {
        const newX = clamp(x + dragOffset.x, 20, canvasSize.width - 20);
        const newY = clamp(y + dragOffset.y, 20, canvasSize.height - 20);
        // Prevent dragging on top of another node
        const tooClose = prev.some((other) =>
          other.id !== node.id && Math.hypot(other.x - newX, other.y - newY) < 44);
        if (tooClose) return node;
        return { ...node, x: newX, y: newY };
      }
      return node;
    }));
  };
  const handleMouseUp = (e2) => {
    if (readOnly) return;
    const canvas = canvasRef.current;
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvasSize.width / rect.width;
    const scaleY = canvasSize.height / rect.height;
    const sx = (e2.clientX - rect.left) * scaleX;
    const sy = (e2.clientY - rect.top) * scaleY;
    const { x, y } = screenToWorld(sx, sy);
    const node = findNodeAt(x, y);
    if (draggingNodeId !== null && isDragging) {
      setIsDragging(false);
      setDraggingNodeId(null);
      return;
    }
    // Walk selection mode: click vertices in order to build a path
    if (selectMode === "walk") {
      if (node) {
        setWalkPath((prev) => {
          if (prev.length === 0) return [node.id];
          const last = prev[prev.length - 1];
          if (node.id === last) {
            // Click same vertex: undo last step
            return prev.slice(0, -1);
          }
          // Check adjacency: there must be an edge from last to node
          const key = sortedKey(last, node.id);
          const edge = edges.get(key);
          if (edge && edge.color === "red") {
            if (directed && edge.from !== undefined) {
              if (edge.from === last && edge.to === node.id) return [...prev, node.id];
            } else {
              return [...prev, node.id];
            }
          }
          setStatus(`No edge from ${last} to ${node.id}`);
          return prev;
        });
        setStatus(`Walk: [${walkPath.join(" → ")}${walkPath.length > 0 ? " → " : ""}${node.id}]`);
      }
      setIsDragging(false);
      setDraggingNodeId(null);
      return;
    }
    // Subgraph selection mode: click to select/deselect edges and vertices
    if (selectMode === "subgraph") {
      if (node) {
        setSelectedVerts((prev) => {
          const next = new Set(prev);
          if (next.has(node.id)) next.delete(node.id);
          else next.add(node.id);
          return next;
        });
        setStatus(selectedVerts.has(node.id) ? `Deselected vertex ${node.id}` : `Selected vertex ${node.id}`);
      } else {
        const edgeKey = findEdgeAt(x, y);
        if (edgeKey) {
          setSelectedEdges((prev) => {
            const next = new Set(prev);
            if (next.has(edgeKey)) next.delete(edgeKey);
            else next.add(edgeKey);
            return next;
          });
          const [aId, bId] = edgeKey.split("-").map(Number);
          setSelectedVerts((prev) => {
            const next = new Set(prev);
            next.add(aId);
            next.add(bId);
            return next;
          });
          setStatus(selectedEdges.has(edgeKey) ? `Deselected edge ${edgeKey}` : `Selected edge ${edgeKey}`);
        }
      }
      setIsDragging(false);
      setDraggingNodeId(null);
      return;
    }
    if (node) {
      if (selectedNodeId === null) {
        setSelectedNodeId(node.id);
        setSelectedEdgeId(null);
        setStatus(`Selected node ${node.id}`);
      } else {
        toggleEdge(selectedNodeId, node.id);
        setSelectedNodeId(null);
      }
    } else if (draggingNodeId === null) {
      const edgeKey = findEdgeAt(x, y);
      if (edgeKey) {
        setSelectedEdgeId(edgeKey);
        setSelectedNodeId(null);
        edgeTypingRef.current = false;
        const edge = edges.get(edgeKey);
        const w = edge && edge.weight !== undefined ? edge.weight : 1;
        setStatus(`Selected edge ${edgeKey} (weight: ${w}) — type a number to change`);
      } else {
        addNode(x, y);
        setSelectedEdgeId(null);
        setSelectedNodeId(null);
      }
    }
    setIsDragging(false);
    setDraggingNodeId(null);
  };
  const handleContextMenu = (e2) => {
    e2.preventDefault();
  };
  const handleWheel = (e2) => {
    e2.preventDefault();
    const delta = e2.deltaY > 0 ? 0.9 : 1.1;
    setZoom((prev) => Math.max(0.3, Math.min(3, prev * delta)));
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
  const applyConcentricLayout = () => {
    const n = nodes.length;
    if (n === 0) return;
    pushHistory();
    const cx = canvasSize.width / 2;
    const cy = canvasSize.height / 2;
    const outerR = Math.min(canvasSize.width, canvasSize.height) / 2 - 40;
    const innerR = outerR * 0.5;
    // Split: first half on outer ring, second half on inner ring.
    const outerCount = Math.ceil(n / 2);
    setNodes((prev) => prev.map((node, i) => {
      if (i < outerCount) {
        const angle = 2 * Math.PI * i / outerCount - Math.PI / 2;
        return { ...node, x: cx + outerR * Math.cos(angle), y: cy + outerR * Math.sin(angle) };
      } else {
        const k = i - outerCount;
        const innerCount = n - outerCount;
        const angle = 2 * Math.PI * k / innerCount - Math.PI / 2;
        return { ...node, x: cx + innerR * Math.cos(angle), y: cy + innerR * Math.sin(angle) };
      }
    }));
    setStatus("Applied concentric layout (outer/inner rings)");
  };
  const applyHubLayout = () => {
    const n = nodes.length;
    if (n === 0) return;
    pushHistory();
    const cx = canvasSize.width / 2;
    const cy = canvasSize.height / 2;
    const radius = Math.min(canvasSize.width, canvasSize.height) / 2 - 40;
    // Vertex 0 (or highest-degree) at center, rest on a circle.
    const degree = (id) => {
      let d = 0;
      edges.forEach((e, key) => {
        if (e.color !== "red") return;
        const [a, b] = key.split("-").map(Number);
        if (a === id || b === id) d++;
      });
      return d;
    };
    let hubId = nodes[0].id, hubDeg = -1;
    for (const nd of nodes) {
      const d = degree(nd.id);
      if (d > hubDeg) { hubDeg = d; hubId = nd.id; }
    }
    const rim = nodes.filter((nd) => nd.id !== hubId);
    setNodes((prev) => prev.map((node) => {
      if (node.id === hubId) return { ...node, x: cx, y: cy };
      const k = rim.findIndex((r) => r.id === node.id);
      const angle = 2 * Math.PI * k / rim.length - Math.PI / 2;
      return { ...node, x: cx + radius * Math.cos(angle), y: cy + radius * Math.sin(angle) };
    }));
    setStatus("Applied hub layout (center + rim)");
  };
  const applyCubeLayout = () => {
    const n = nodes.length;
    if (n === 0) return;
    // Only meaningful when n = 2^d; place each vertex by its bit pattern.
    const d = Math.round(Math.log2(n));
    if (2 ** d !== n) { applyConcentricLayout(); return; }
    pushHistory();
    const cx = canvasSize.width / 2;
    const cy = canvasSize.height / 2;
    const size = Math.min(canvasSize.width, canvasSize.height) / 2 - 40;
    // Assign each dimension its own 2D basis vector so no two vertices collide.
    // bit 0 → +x, bit 1 → +y, bit 2 → small diagonal, bit 3 → smaller anti-diagonal.
    const basis = [
      { x: 1.0, y: 0.0 },
      { x: 0.0, y: 1.0 },
      { x: 0.45, y: 0.45 },
      { x: 0.45, y: -0.45 }
    ];
    // Total extent for normalization.
    let maxExt = 0;
    for (let bit = 0; bit < d; bit++) maxExt += Math.abs(basis[bit].x) + 0;
    setNodes((prev) => prev.map((node, i) => {
      let x = 0, y = 0;
      for (let bit = 0; bit < d; bit++) {
        const set = (i >> bit) & 1 ? 1 : -1;
        const b = basis[bit] || { x: 0, y: 0 };
        x += set * b.x;
        y += set * b.y;
      }
      const norm = Math.max(1, maxExt);
      return { ...node, x: cx + (x / norm) * size * 0.9, y: cy + (y / norm) * size * 0.9 };
    }));
    setStatus("Applied cube layout");
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
  const applyLayout = (name) => {
    if (name === "circle") applyCircleLayout();
    else if (name === "concentric") applyConcentricLayout();
    else if (name === "hub") applyHubLayout();
    else if (name === "cube") applyCubeLayout();
    else if (name === "spring") applySpringLayout();
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
  const buildWalkLean = () => {
    if (walkPath.length < 2) return null;
    const idToIndex = new Map(nodes.map((nd, i) => [nd.id, i]));
    if (directed) {
      // Directed: Walk.cons (v := next) (by decide) ...
      let result = "Walk.nil";
      for (let i = walkPath.length - 2; i >= 0; i--) {
        const vIdx = idToIndex.get(walkPath[i + 1]);
        result = `Walk.cons (v := ${vIdx}) (by decide) (${result})`;
      }
      return result;
    } else {
      // Undirected: SimpleGraph.Walk.cons (u := cur) (v := next) (by decide) ...
      let result = "SimpleGraph.Walk.nil";
      for (let i = walkPath.length - 2; i >= 0; i--) {
        const uIdx = idToIndex.get(walkPath[i]);
        const vIdx = idToIndex.get(walkPath[i + 1]);
        result = `SimpleGraph.Walk.cons (u := ${uIdx}) (v := ${vIdx}) (by decide) (${result})`;
      }
      return result;
    }
  };
  const buildSubgraphMatrixLean = () => {
    const n = nodes.length;
    if (n === 0 || selectedEdges.size === 0) return null;
    const idToIndex = new Map(nodes.map((nd, i) => [nd.id, i]));
    const matrix = Array.from({ length: n }, () => Array(n).fill(0));
    selectedEdges.forEach((key) => {
      const [a, b] = key.split("-").map(Number);
      const i = idToIndex.get(a);
      const j = idToIndex.get(b);
      if (i === undefined || j === undefined) return;
      const edge = edges.get(key);
      if (directed && edge && edge.from !== undefined) {
        const fi = idToIndex.get(edge.from);
        const ti = idToIndex.get(edge.to);
        if (fi !== undefined && ti !== undefined) matrix[fi][ti] = 1;
      } else {
        matrix[i][j] = 1;
        matrix[j][i] = 1;
      }
    });
    const rows = matrix.map((row) => row.join(", ")).join(";\n      ");
    return `!![
      ${rows}]`;
  };
  const buildAdjMatrixLean = () => {
    const n = nodes.length;
    if (n === 0) return "!![]";
    const idToIndex = new Map(nodes.map((nd, i) => [nd.id, i]));
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
    const rows = matrix.map((row) => row.join(", ")).join(";\n      ");
    return `!![
      ${rows}]`;
  };
  const verifyExport = () => {
    const n = nodes.length;
    if (n === 0) return true;
    const idToIndex = new Map(nodes.map((nd, i) => [nd.id, i]));
    const matrix = Array.from({ length: n }, () => Array(n).fill(0));
    edges.forEach((edgeData, key) => {
      if (edgeData.color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const i = idToIndex.get(a);
      const j = idToIndex.get(b);
      if (i === void 0 || j === void 0) return;
      const val = weighted && edgeData.weight !== undefined ? edgeData.weight : 1;
      if (directed && edgeData.from !== undefined) {
        const fi = idToIndex.get(edgeData.from);
        const ti = idToIndex.get(edgeData.to);
        if (fi !== void 0 && ti !== void 0) matrix[fi][ti] = val;
      } else {
        matrix[i][j] = val;
        matrix[j][i] = val;
      }
    });
    // Check 1: every red edge has a nonzero matrix entry
    let ok = true;
    edges.forEach((edgeData, key) => {
      if (edgeData.color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const i = idToIndex.get(a);
      const j = idToIndex.get(b);
      if (i === void 0 || j === void 0) { ok = false; return; }
      if (directed && edgeData.from !== undefined) {
        const fi = idToIndex.get(edgeData.from);
        const ti = idToIndex.get(edgeData.to);
        if (fi === void 0 || ti === void 0 || matrix[fi][ti] === 0) ok = false;
      } else {
        if (matrix[i][j] === 0) ok = false;
      }
    });
    // Check 2: every nonzero matrix entry has a corresponding red edge
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        if (matrix[i][j] !== 0) {
          const ni = nodes[i], nj = nodes[j];
          const key = sortedKey(ni.id, nj.id);
          const edge = edges.get(key);
          if (!edge || edge.color !== "red") ok = false;
        }
      }
    }
    return ok;
  };
  const hasGraphChanged = () => {
    const init = initMatrix;
    if (init.length === 0 && nodes.length === 0) return false;
    if (init.length !== nodes.length) return true;
    const n = nodes.length;
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        const initVal = init[i] && init[i][j] ? init[i][j] : 0;
        let curVal = 0;
        const ni = nodes[i], nj = nodes[j];
        if (ni && nj) {
          const key = sortedKey(ni.id, nj.id);
          const edge = edges.get(key);
          if (edge && edge.color === "red") {
            if (directed && edge.from !== undefined) {
              // For directed: only count if this is the correct direction
              const fromIdx = nodes.findIndex((nd) => nd.id === edge.from);
              const toIdx = nodes.findIndex((nd) => nd.id === edge.to);
              if (fromIdx === i && toIdx === j) {
                curVal = weighted && edge.weight !== undefined ? edge.weight : 1;
              }
            } else {
              curVal = weighted && edge.weight !== undefined ? edge.weight : 1;
            }
          }
        }
        if (initVal !== curVal) return true;
      }
    }
    return false;
  };
  const sendToLean = () => {
    const graphChanged = hasGraphChanged();
    if (graphChanged && !verifyExport()) {
      setStatus("Export verification failed: edge data mismatch");
      return;
    }
    setStatus("Sending to Lean...");
    rs.call("graphWidget.updateGraph", {
      adjMatrix: graphChanged ? buildAdjMatrixLean() : "",
      subgraphMatrix: selectMode === "subgraph" ? (buildSubgraphMatrixLean() || "") : "",
      walkExpr: selectMode === "walk" ? (buildWalkLean() || "") : "",
      walkStart: selectMode === "walk" && walkPath.length >= 2 ? String(nodes.findIndex((nd) => nd.id === walkPath[0])) : "",
      walkEnd: selectMode === "walk" && walkPath.length >= 2 ? String(nodes.findIndex((nd) => nd.id === walkPath[walkPath.length - 1])) : "",
      graphIdent: props.graphIdent || "",
      directed: directed,
      weighted: weighted,
      readOnly: false,
      initialMatrix: [],
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
      setStatus("Graph sent to Lean successfully");
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
    fontFamily: "'Inter', system-ui, -apple-system, sans-serif",
    background: "linear-gradient(145deg, rgba(15, 23, 42, 0.95), rgba(10, 14, 30, 0.98))",
    color: "#e2e8f0",
    borderRadius: "14px",
    overflow: "hidden",
    border: "1px solid rgba(255, 255, 255, 0.08)",
    boxShadow: "0 20px 60px rgba(0, 0, 0, 0.4), 0 0 0 1px rgba(255, 255, 255, 0.05) inset"
  } }, [
    // Header
    e("div", { style: {
      padding: "14px 20px",
      background: "rgba(255, 255, 255, 0.03)",
      backdropFilter: "blur(12px)",
      WebkitBackdropFilter: "blur(12px)",
      borderBottom: "1px solid rgba(255, 255, 255, 0.06)"
    } }, [
      e("div", { style: { display: "flex", alignItems: "center", justifyContent: "space-between", marginBottom: readOnly ? "0" : "10px" } }, [
        e("h3", { style: { margin: 0, fontSize: "14px", fontWeight: "600", letterSpacing: "-0.01em", color: "#f1f5f9" } },
          readOnly ? "Graph Viewer" : "Graph Widget"),
        e("div", { style: { display: "flex", gap: "6px" } }, [
          e("span", { style: {
            padding: "3px 10px",
            background: "rgba(99, 102, 241, 0.12)",
            borderRadius: "999px",
            fontSize: "11px",
            fontWeight: "500",
            color: "#a5b4fc",
            border: "1px solid rgba(99, 102, 241, 0.2)"
          } }, `${nodes.length} nodes`),
          e("span", { style: {
            padding: "3px 10px",
            background: "rgba(244, 63, 94, 0.1)",
            borderRadius: "999px",
            fontSize: "11px",
            fontWeight: "500",
            color: "#fda4af",
            border: "1px solid rgba(244, 63, 94, 0.2)"
          } }, `${edgeCount} edges`),
          directed ? e("span", { style: {
            padding: "3px 10px",
            background: "rgba(251, 191, 36, 0.1)",
            borderRadius: "999px",
            fontSize: "11px",
            fontWeight: "500",
            color: "#fcd34d",
            border: "1px solid rgba(251, 191, 36, 0.2)"
          } }, "directed") : null,
          weighted ? e("span", { style: {
            padding: "3px 10px",
            background: "rgba(52, 211, 153, 0.1)",
            borderRadius: "999px",
            fontSize: "11px",
            fontWeight: "500",
            color: "#6ee7b7",
            border: "1px solid rgba(52, 211, 153, 0.2)"
          } }, "weighted") : null,
        ])
      ]),
      !readOnly ? e("div", { style: { display: "flex", gap: "6px", flexWrap: "wrap", alignItems: "center" } }, [
        e("button", {
          onClick: clearGraph,
          style: {
            border: "1px solid rgba(239, 68, 68, 0.2)",
            background: "rgba(239, 68, 68, 0.08)",
            backdropFilter: "blur(8px)",
            WebkitBackdropFilter: "blur(8px)",
            color: "#fca5a5",
            padding: "7px 12px",
            borderRadius: "8px",
            cursor: "pointer",
            fontSize: "11px",
            fontWeight: "500",
            transition: "all 0.2s ease"
          }
        }, "Clear graph"),
        e("button", {
          onClick: undo,
          style: btnStyle
        }, "Undo (Ctrl+Z)"),
        e("select", {
          value: graphMode,
          onChange: (ev) => switchGraphMode(ev.target.value),
          style: {
            border: "1px solid rgba(255, 255, 255, 0.12)",
            background: "rgba(255, 255, 255, 0.06)",
            color: "#e2e8f0",
            padding: "7px 12px",
            borderRadius: "8px",
            fontSize: "11px",
            fontWeight: "500",
            cursor: "pointer",
            appearance: "none",
            WebkitAppearance: "none",
            paddingRight: "28px",
            backgroundImage: "url(\"data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='10' height='6'%3E%3Cpath d='M0 0l5 6 5-6z' fill='%2394a3b8'/%3E%3C/svg%3E\")",
            backgroundRepeat: "no-repeat",
            backgroundPosition: "right 10px center"
          }
        }, [
          e("option", { value: "simple" }, "Simple graph"),
          e("option", { value: "colored" }, "Bi-colored graph")
        ]),
        e("label", { style: { fontSize: "11px", display: "flex", alignItems: "center", gap: "5px", cursor: "pointer", color: "#94a3b8", fontWeight: "500" } }, [
          e("input", {
            type: "checkbox",
            checked: directed,
            onChange: (ev) => setDirected(ev.target.checked),
            style: { accentColor: "#6366f1" }
          }),
          "Directed"
        ]),
        e("label", { style: { fontSize: "11px", display: "flex", alignItems: "center", gap: "5px", cursor: "pointer", color: "#94a3b8", fontWeight: "500" } }, [
          e("input", {
            type: "checkbox",
            checked: weighted,
            onChange: (ev) => {
              const nowWeighted = ev.target.checked;
              setWeighted(nowWeighted);
              if (nowWeighted) {
                setEdges((prev) => {
                  const newEdges = new Map(prev);
                  newEdges.forEach((val, key) => {
                    if (val.color === "red" && val.weight === undefined) {
                      newEdges.set(key, { ...val, weight: 1 });
                    }
                  });
                  return newEdges;
                });
              }
            },
            style: { accentColor: "#6366f1" }
          }),
          "Weighted"
        ]),
        weighted ? e("label", { style: { fontSize: "11px", display: "flex", alignItems: "center", gap: "5px", color: "#94a3b8" } }, [
          "W:",
          e("input", {
            type: "number",
            value: nextWeight,
            onChange: (ev) => setNextWeight(Number(ev.target.value) || 1),
            style: {
              width: "46px",
              border: "1px solid rgba(255, 255, 255, 0.1)",
              background: "rgba(255, 255, 255, 0.05)",
              color: "#e2e8f0",
              padding: "5px 8px",
              borderRadius: "6px",
              fontSize: "11px"
            }
          })
        ]) : null,
        e("select", {
          value: selectMode,
          onChange: (ev) => {
            const mode = ev.target.value;
            setSelectMode(mode);
            setSelectedEdges(new Set());
            setSelectedVerts(new Set());
            setWalkPath([]);
            setSelectedNodeId(null);
            if (mode === "subgraph") setStatus("Subgraph mode: click edges/vertices to select");
            else if (mode === "walk") setStatus("Walk mode: click vertices in order to build a path");
            else setStatus("Selection off");
          },
          style: {
            border: selectMode !== "none" ? "1px solid rgba(250, 204, 21, 0.4)" : "1px solid rgba(255, 255, 255, 0.12)",
            background: selectMode !== "none" ? "rgba(250, 204, 21, 0.2)" : "rgba(255, 255, 255, 0.06)",
            color: selectMode !== "none" ? "#fde047" : "#e2e8f0",
            padding: "7px 12px",
            borderRadius: "8px",
            fontSize: "11px",
            fontWeight: "500",
            cursor: "pointer",
            appearance: "none",
            WebkitAppearance: "none",
            paddingRight: "28px",
            backgroundImage: "url(\"data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='10' height='6'%3E%3Cpath d='M0 0l5 6 5-6z' fill='%2394a3b8'/%3E%3C/svg%3E\")",
            backgroundRepeat: "no-repeat",
            backgroundPosition: "right 10px center"
          }
        }, [
          e("option", { value: "none" }, "No selection"),
          e("option", { value: "subgraph" }, "Select Subgraph"),
          e("option", { value: "walk" }, "Select Walk")
        ]),
        e("select", {
          value: "",
          onChange: (ev) => { applyLayout(ev.target.value); ev.target.value = ""; },
          style: {
            border: "1px solid rgba(255, 255, 255, 0.12)",
            background: "rgba(255, 255, 255, 0.06)",
            color: "#e2e8f0",
            padding: "7px 12px",
            borderRadius: "8px",
            fontSize: "11px",
            fontWeight: "500",
            cursor: "pointer",
            appearance: "none",
            WebkitAppearance: "none",
            paddingRight: "28px",
            backgroundImage: "url(\"data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='10' height='6'%3E%3Cpath d='M0 0l5 6 5-6z' fill='%2394a3b8'/%3E%3C/svg%3E\")",
            backgroundRepeat: "no-repeat",
            backgroundPosition: "right 10px center"
          }
        }, [
          e("option", { value: "" }, "Layout…"),
          e("option", { value: "circle" }, "Circular"),
          e("option", { value: "concentric" }, "Concentric"),
          e("option", { value: "hub" }, "Hub"),
          e("option", { value: "cube" }, "Cube"),
          e("option", { value: "spring" }, "Spring")
        ]),
        e("button", {
          onClick: () => setShowLabels(!showLabels),
          style: showLabels ? {
            ...btnStyle,
            background: "rgba(52, 211, 153, 0.2)",
            border: "1px solid rgba(52, 211, 153, 0.4)",
            color: "#6ee7b7"
          } : btnStyle
        }, "Labels")
      ]) : null
    ]),
    // Canvas
    e("div", { style: {
      display: "flex",
      justifyContent: "center",
      background: "#080d1a",
      borderTop: "1px solid rgba(255, 255, 255, 0.03)",
      borderBottom: "1px solid rgba(255, 255, 255, 0.03)",
      overflow: "auto",
      maxHeight: "450px"
    } },
      e("canvas", {
        ref: canvasRef,
        onMouseDown: handleMouseDown,
        onMouseMove: handleMouseMove,
        onMouseUp: handleMouseUp,
        onWheel: handleWheel,
        onContextMenu: handleContextMenu,
        style: {
          display: "block",
          width: Math.round(canvasSize.width * zoom) + "px",
          height: Math.round(canvasSize.height * zoom) + "px",
          minWidth: canvasSize.width + "px",
          minHeight: canvasSize.height + "px",
          background: "radial-gradient(ellipse at 30% 20%, rgba(99, 102, 241, 0.04), transparent 50%), radial-gradient(ellipse at 70% 80%, rgba(244, 63, 94, 0.03), transparent 50%), #080d1a",
          cursor: readOnly ? "default" : "crosshair"
        }
      })
    ),
    // Bottom panel
    e("div", { style: {
      padding: "14px 20px",
      background: "rgba(255, 255, 255, 0.02)",
      backdropFilter: "blur(12px)",
      WebkitBackdropFilter: "blur(12px)",
      borderTop: "1px solid rgba(255, 255, 255, 0.06)"
    } }, readOnly ? [
      e("div", { style: { display: "flex", gap: "6px", flexWrap: "wrap" } }, [
        e("select", {
          value: graphMode,
          onChange: (ev) => switchGraphMode(ev.target.value),
          style: {
            border: "1px solid rgba(255, 255, 255, 0.12)",
            background: "rgba(255, 255, 255, 0.06)",
            color: "#e2e8f0",
            padding: "7px 12px",
            borderRadius: "8px",
            fontSize: "11px",
            fontWeight: "500",
            cursor: "pointer",
            appearance: "none",
            WebkitAppearance: "none",
            paddingRight: "28px",
            backgroundImage: "url(\"data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='10' height='6'%3E%3Cpath d='M0 0l5 6 5-6z' fill='%2394a3b8'/%3E%3C/svg%3E\")",
            backgroundRepeat: "no-repeat",
            backgroundPosition: "right 10px center"
          }
        }, [
          e("option", { value: "simple" }, "Simple graph"),
          e("option", { value: "colored" }, "Bi-colored graph")
        ]),
        e("select", {
          value: "",
          onChange: (ev) => { applyLayout(ev.target.value); ev.target.value = ""; },
          style: {
            border: "1px solid rgba(255, 255, 255, 0.12)",
            background: "rgba(255, 255, 255, 0.06)",
            color: "#e2e8f0",
            padding: "7px 12px",
            borderRadius: "8px",
            fontSize: "11px",
            fontWeight: "500",
            cursor: "pointer",
            appearance: "none",
            WebkitAppearance: "none",
            paddingRight: "28px",
            backgroundImage: "url(\"data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='10' height='6'%3E%3Cpath d='M0 0l5 6 5-6z' fill='%2394a3b8'/%3E%3C/svg%3E\")",
            backgroundRepeat: "no-repeat",
            backgroundPosition: "right 10px center"
          }
        }, [
          e("option", { value: "" }, "Layout…"),
          e("option", { value: "circle" }, "Circular"),
          e("option", { value: "concentric" }, "Concentric"),
          e("option", { value: "hub" }, "Hub"),
          e("option", { value: "cube" }, "Cube"),
          e("option", { value: "spring" }, "Spring")
        ]),
        (!directed && !weighted) ? e("button", {
          onClick: () => {
            navigator.clipboard.writeText(graph6String);
            setStatus("Copied graph6 to clipboard");
          },
          style: btnStyle
        }, "Copy graph6") : null,
        e("button", {
          onClick: () => {
            navigator.clipboard.writeText(exportAdjMatrix());
            setStatus("Copied adjacency matrix to clipboard");
          },
          style: btnStyle
        }, "Copy matrix"),
        e("button", {
          onClick: () => {
            navigator.clipboard.writeText(exportEdgeList());
            setStatus("Copied edge list to clipboard");
          },
          style: btnStyle
        }, "Copy edges"),
        e("button", {
          onClick: () => {
            const canvas = canvasRef.current;
            if (!canvas) return;
            // Export at 4x resolution for print quality
            const dpr = 4;
            const exportCanvas = document.createElement("canvas");
            exportCanvas.width = canvasSize.width * dpr;
            exportCanvas.height = canvasSize.height * dpr;
            const ctx = exportCanvas.getContext("2d");
            ctx.drawImage(canvas, 0, 0, exportCanvas.width, exportCanvas.height);
            const link = document.createElement("a");
            link.download = "graph.png";
            link.href = exportCanvas.toDataURL("image/png");
            link.click();
            setStatus("Exported high-res PNG (4x)");
          },
          style: btnStyle
        }, "Export PNG")
      ]),
      e("div", { style: {
        fontSize: "10px",
        color: "#64748b",
        marginTop: "8px",
        letterSpacing: "0.02em"
      } }, status)
    ] : [
      e("div", { style: {
        fontSize: "10px",
        color: "#64748b",
        marginBottom: "10px",
        letterSpacing: "0.02em"
      } }, "Click to add node · Select two nodes to toggle edge · Drag to move · Right-click to delete · Ctrl+Z undo"),
      e("div", { style: { display: "flex", gap: "6px", marginBottom: "10px", flexWrap: "wrap" } }, [
        e("button", {
          onClick: sendToLean,
          style: {
            background: "linear-gradient(135deg, rgba(99, 102, 241, 0.9), rgba(139, 92, 246, 0.9))",
            color: "#ffffff",
            border: "1px solid rgba(139, 92, 246, 0.3)",
            padding: "8px 18px",
            borderRadius: "8px",
            cursor: "pointer",
            fontWeight: "600",
            fontSize: "12px",
            letterSpacing: "0.01em",
            boxShadow: "0 4px 16px rgba(99, 102, 241, 0.25)",
            transition: "all 0.2s ease"
          }
        }, "Send to Lean"),
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
        }, "Copy matrix"),
        e("button", {
          onClick: () => {
            const canvas = canvasRef.current;
            if (!canvas) return;
            // Export at 4x resolution for print quality
            const dpr = 4;
            const exportCanvas = document.createElement("canvas");
            exportCanvas.width = canvasSize.width * dpr;
            exportCanvas.height = canvasSize.height * dpr;
            const ctx = exportCanvas.getContext("2d");
            ctx.drawImage(canvas, 0, 0, exportCanvas.width, exportCanvas.height);
            const link = document.createElement("a");
            link.download = "graph.png";
            link.href = exportCanvas.toDataURL("image/png");
            link.click();
            setStatus("Exported high-res PNG (4x)");
          },
          style: btnStyle
        }, "Export PNG")
      ]),
      e("div", { style: {
        fontSize: "10px",
        fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
        color: "#475569",
        wordBreak: "break-all",
        marginBottom: "6px",
        padding: "6px 10px",
        background: "rgba(0, 0, 0, 0.2)",
        borderRadius: "6px",
        border: "1px solid rgba(255, 255, 255, 0.04)",
        whiteSpace: "pre-wrap"
      } }, (!directed && !weighted) ? `g6: ${graph6String}` : `matrix:\n${exportAdjMatrix()}`),
      e("div", { style: {
        fontSize: "10px",
        color: "#64748b",
        letterSpacing: "0.02em"
      } }, status)
    ])
  ]);
}
export {
  widget_graph_default as default
};
