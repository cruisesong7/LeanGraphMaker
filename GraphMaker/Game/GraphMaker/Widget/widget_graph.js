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
  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) {
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
  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) {
      const key = `${i}-${j}`;
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
  const [selectedNodeId, setSelectedNodeId] = React.useState(null);
  const [draggingNodeId, setDraggingNodeId] = React.useState(null);
  const [dragOffset, setDragOffset] = React.useState({ x: 0, y: 0 });
  const [dragStart, setDragStart] = React.useState({ x: 0, y: 0 });
  const [isDragging, setIsDragging] = React.useState(false);
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
    edges.forEach(({ color }, key) => {
      if (graphMode === "simple" && color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const na = nodes.find((n) => n.id === a);
      const nb = nodes.find((n) => n.id === b);
      if (!na || !nb) return;
      ctx.strokeStyle = color === "blue" ? "rgba(96, 165, 250, 0.85)" : "rgba(248, 113, 113, 0.9)";
      ctx.beginPath();
      ctx.moveTo(na.x, na.y);
      ctx.lineTo(nb.x, nb.y);
      ctx.stroke();
    });
    nodes.forEach((node, index) => {
      const radius = 16;
      const isSelected = node.id === selectedNodeId;
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
    ctx.restore();
  }, [nodes, edges, selectedNodeId, graphMode]);
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
  const addNode = (x, y) => {
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
    const key = sortedKey(aId, bId);
    setEdges((prev) => {
      const newEdges = new Map(prev);
      const existing = newEdges.get(key);
      if (graphMode === "colored") {
        if (!existing || existing.color === "blue") {
          newEdges.set(key, { color: "red" });
          setStatus(`Edge ${key} set to red (connected)`);
        } else {
          newEdges.set(key, { color: "blue" });
          setStatus(`Edge ${key} set to blue (disconnected)`);
        }
      } else {
        if (existing && existing.color === "red") {
          newEdges.delete(key);
          setStatus(`Edge ${key} removed`);
        } else {
          newEdges.set(key, { color: "red" });
          setStatus(`Edge ${key} added`);
        }
      }
      return newEdges;
    });
  };
  const deleteNode = (nodeId) => {
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
    const canvas = canvasRef.current;
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    const x = (e2.clientX - rect.left) * scaleX;
    const y = (e2.clientY - rect.top) * scaleY;
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
    }
  };
  const handleMouseMove = (e2) => {
    if (draggingNodeId === null) return;
    const canvas = canvasRef.current;
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    const x = (e2.clientX - rect.left) * scaleX;
    const y = (e2.clientY - rect.top) * scaleY;
    const moved = Math.hypot(x - dragStart.x, y - dragStart.y) > 3;
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
    const canvas = canvasRef.current;
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    const x = (e2.clientX - rect.left) * scaleX;
    const y = (e2.clientY - rect.top) * scaleY;
    const node = findNodeAt(x, y);
    if (draggingNodeId !== null && isDragging) {
      setIsDragging(false);
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
  const handleContextMenu = (e2) => {
    e2.preventDefault();
  };
  const applyCircleLayout = () => {
    const n = nodes.length;
    if (n === 0) return;
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
    setNodes([]);
    setEdges(/* @__PURE__ */ new Map());
    setSelectedNodeId(null);
    setStatus("Graph cleared");
  };
  const sendToLean = () => {
    setStatus("Sending to Lean...");
    rs.call("graphWidget.updateGraph", {
      graph6: graph6String,
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
    edges.forEach(({ color }, key) => {
      if (color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const ia = idToIndex.get(a);
      const ib = idToIndex.get(b);
      if (ia !== void 0 && ib !== void 0) {
        lines.push(`${ia} ${ib}`);
      }
    });
    return lines.join("\n");
  };
  const exportAdjMatrix = () => {
    const n = nodes.length;
    const idToIndex = new Map(nodes.map((n2, i) => [n2.id, i]));
    const matrix = Array.from({ length: n }, () => Array(n).fill(0));
    edges.forEach(({ color }, key) => {
      if (color !== "red") return;
      const [a, b] = key.split("-").map(Number);
      const i = idToIndex.get(a);
      const j = idToIndex.get(b);
      if (i !== void 0 && j !== void 0) {
        matrix[i][j] = 1;
        matrix[j][i] = 1;
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
          style: {
            border: "1px solid rgba(255, 255, 255, 0.15)",
            background: "rgba(255, 255, 255, 0.08)",
            color: "inherit",
            padding: "6px 10px",
            borderRadius: "6px",
            cursor: "pointer",
            fontSize: "12px"
          }
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
        e("select", {
          value: graphMode,
          onChange: (ev) => setGraphMode(ev.target.value),
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
        e("button", {
          onClick: applyCircleLayout,
          style: {
            border: "1px solid rgba(255, 255, 255, 0.15)",
            background: "rgba(255, 255, 255, 0.08)",
            color: "inherit",
            padding: "6px 10px",
            borderRadius: "6px",
            cursor: "pointer",
            fontSize: "12px"
          }
        }, "Circle layout"),
        e("button", {
          onClick: applySpringLayout,
          style: {
            border: "1px solid rgba(255, 255, 255, 0.15)",
            background: "rgba(255, 255, 255, 0.08)",
            color: "inherit",
            padding: "6px 10px",
            borderRadius: "6px",
            cursor: "pointer",
            fontSize: "12px"
          }
        }, "Spring layout")
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
      onContextMenu: handleContextMenu,
      style: {
        display: "block",
        width: "100%",
        background: "radial-gradient(circle at 50% 50%, rgba(255, 255, 255, 0.04), transparent 60%), #0b1224",
        cursor: "crosshair"
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
      } }, "Click empty space to add a node. Click two nodes to toggle edge. Drag to reposition. Right-click to delete."),
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
        e("button", {
          onClick: () => {
            navigator.clipboard.writeText(graph6String);
            setStatus("Copied graph6 to clipboard");
          },
          style: {
            border: "1px solid rgba(255, 255, 255, 0.15)",
            background: "rgba(255, 255, 255, 0.08)",
            color: "inherit",
            padding: "8px 12px",
            borderRadius: "6px",
            cursor: "pointer",
            fontSize: "12px"
          }
        }, "Copy graph6"),
        e("button", {
          onClick: () => {
            navigator.clipboard.writeText(exportEdgeList());
            setStatus("Copied edge list to clipboard");
          },
          style: {
            border: "1px solid rgba(255, 255, 255, 0.15)",
            background: "rgba(255, 255, 255, 0.08)",
            color: "inherit",
            padding: "8px 12px",
            borderRadius: "6px",
            cursor: "pointer",
            fontSize: "12px"
          }
        }, "Copy edges"),
        e("button", {
          onClick: () => {
            navigator.clipboard.writeText(exportAdjMatrix());
            setStatus("Copied adjacency matrix to clipboard");
          },
          style: {
            border: "1px solid rgba(255, 255, 255, 0.15)",
            background: "rgba(255, 255, 255, 0.08)",
            color: "inherit",
            padding: "8px 12px",
            borderRadius: "6px",
            cursor: "pointer",
            fontSize: "12px"
          }
        }, "Copy matrix")
      ]),
      e("div", { style: {
        fontSize: "11px",
        fontFamily: "monospace",
        color: "#94a3b8",
        wordBreak: "break-all",
        marginBottom: "4px"
      } }, `graph6: ${graph6String}`),
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
