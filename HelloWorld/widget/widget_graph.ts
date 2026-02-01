/**
 * Graph Widget for Lean Infoview
 * 
 * This widget provides an interactive graph drawing canvas that integrates with Lean's
 * theorem prover environment. Users can create, edit, and visualize graphs, then send
 * the graph data back to Lean for formal verification or analysis.
 * 
 * ## How to Use from Lean:
 * 
 * 1. **Import the widget in your Lean file:**
 * ```lean
 * import Lean.Widget.UserWidget
 * import ProofWidgets.Component.Basic
 * 
 * @[widget_module]
 * def GraphWidget : Component GraphWidgetProps where
 *   javascript := include_str "../widget/widget_graph.js"
 * ```
 * 
 * 2. **Define the props structure in Lean:**
 * ```lean
 * structure GraphWidgetProps where
 *   graph6 : String          -- Initial graph in graph6 format (e.g., "D??" for empty 4-node graph)
 *   replaceRange : Option Lsp.Range  -- Range in the document to replace when sending back
 * ```
 * 
 * 3. **Create a command to display the widget:**
 * ```lean
 * #eval show MetaM Unit from do
 *   savePanelWidgetInfo GraphWidget.javascript
 *     (GraphWidgetProps.mk "D??" none)  -- Start with empty 4-node graph
 * ```
 * 
 * 4. **Implement the RPC handler in Lean:**
 * ```lean
 * @[server_rpc_method]
 * def graphWidget.updateGraph (params : GraphUpdateParams) : RequestM (RequestTask GraphUpdateResult) := do
 *   -- params contains:
 *   --   - graph6: String       (the graph6 encoded string)
 *   --   - replaceRange: Option (the range to replace)
 *   -- 
 *   -- Return DocumentEdit to insert the graph6 string into the Lean file
 *   return { 
 *     edit: <create document edit>,
 *     newSelection: <optional new cursor position>
 *   }
 * ```
 * 
 * ## Widget Features:
 * 
 * - **Interactive Canvas**: Click to add nodes, click two nodes to create edges
 * - **Drag & Drop**: Reposition nodes by dragging
 * - **Two Graph Modes**:
 *   - Simple: Add/remove edges freely
 *   - Bi-colored: Complete graph with red (connected) and blue (disconnected) edges
 * - **Layout Algorithms**: Circle layout and force-directed spring layout
 * - **Export Formats**: graph6, edge list, adjacency matrix
 * - **Bidirectional Communication**: 
 *   - Receive initial graph from Lean (via props.graph6)
 *   - Send modified graph back to Lean (via RPC call)
 * 
 * ## Graph6 Format:
 * 
 * graph6 is a compact ASCII encoding for simple undirected graphs:
 * - First character: n + 63 (where n is the number of nodes, max 62)
 * - Remaining characters: encode the upper triangle of the adjacency matrix
 * - Example: "D??" = 4 nodes with no edges
 * - Example: "D`o" = 4 nodes with edges 0-1, 0-2, 1-3
 * 
 * ## Data Flow:
 * 
 * Lean → Widget:
 *   props.graph6 (string) → parseGraph6() → visual graph on canvas
 * 
 * Widget → Lean:
 *   user edits graph → toGraph6() → RPC call → Lean receives graph6 string
 * 
 * @author Brian Li
 * @module widget_graph
 */

import { RpcContext, EditorContext, mapRpcError } from '@leanprover/infoview'
import * as React from 'react';

const e = React.createElement;

// ============================================================================
// Type Definitions
// ============================================================================

/**
 * Represents a node in the graph with position information.
 * The id is used for edge references, while x,y are canvas coordinates.
 */
interface Node {
  id: number;      // Unique identifier for the node
  x: number;       // X coordinate on canvas
  y: number;       // Y coordinate on canvas
}

/**
 * Edge data with color information.
 * Red edges are "connected" (exported in graph6), blue edges are "disconnected"
 * (only used in bi-colored mode to represent the complete graph).
 */
interface EdgeData {
  color: 'red' | 'blue';
}

// ============================================================================
// Graph6 Encoding/Decoding Functions
// ============================================================================

/**
 * Parse a graph6 string into nodes and edges.
 * 
 * graph6 format specification:
 * - First byte encodes n (number of vertices): char = n + 63
 * - Remaining bytes encode upper triangle of adjacency matrix
 * - Each byte encodes 6 bits (values 0-63, stored as ASCII 63-126)
 * 
 * @param g6 - The graph6 encoded string
 * @param canvasWidth - Width of the canvas for initial node layout
 * @param canvasHeight - Height of the canvas for initial node layout
 * @returns Object containing nodes array and edges map
 * 
 * @example
 * parseGraph6("D??", 600, 400)  // Returns 4 nodes, 0 edges
 * parseGraph6("C~", 600, 400)   // Returns 4 nodes, all edges (complete graph)
 */
function parseGraph6(g6: string, canvasWidth: number, canvasHeight: number): { 
  nodes: Node[]; 
  edges: Map<string, EdgeData> 
} {
  if (!g6 || g6 === "?") return { nodes: [], edges: new Map() };
  
  const n = g6.charCodeAt(0) - 63;
  if (n < 0 || n > 62) return { nodes: [], edges: new Map() };
  
  const payload = g6.slice(1);
  const bits: number[] = [];
  
  for (let i = 0; i < payload.length; i++) {
    let chunk = payload.charCodeAt(i) - 63;
    for (let j = 5; j >= 0; j--) {
      bits.push((chunk >> j) & 1);
    }
  }
  
  const edges = new Map<string, EdgeData>();
  let bitIndex = 0;
  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) {
      if (bits[bitIndex] === 1) {
        edges.set(`${i}-${j}`, { color: 'red' });
      }
      bitIndex++;
    }
  }
  
  // Create nodes in a circle layout
  const nodes: Node[] = [];
  const radius = Math.min(canvasWidth, canvasHeight) / 2 - 40;
  const cx = canvasWidth / 2;
  const cy = canvasHeight / 2;
  
  for (let i = 0; i < n; i++) {
    const angle = (2 * Math.PI * i) / n;
    nodes.push({
      id: i,
      x: cx + radius * Math.cos(angle),
      y: cy + radius * Math.sin(angle)
    });
  }
  
  return { nodes, edges };
}

/**
 * Convert nodes and edges to graph6 format.
 * 
 * Only red edges are encoded (blue edges are ignored).
 * This is the format that will be sent back to Lean.
 * 
 * @param nodes - Array of nodes in the graph
 * @param edges - Map of edges with color information
 * @returns graph6 encoded string, or "?" if empty/invalid
 * 
 * @example
 * toGraph6([{id:0,x:0,y:0}, {id:1,x:1,y:1}], new Map([["0-1", {color:"red"}]]))
 * // Returns a graph6 string encoding 2 nodes with 1 edge
 */
function toGraph6(nodes: Node[], edges: Map<string, EdgeData>): string {
  const n = nodes.length;
  if (n === 0) return "?";
  if (n > 62) return "?";
  
  const header = String.fromCharCode(n + 63);
  const bits: number[] = [];
  
  for (let i = 0; i < n; i++) {
    for (let j = i + 1; j < n; j++) {
      const key = `${i}-${j}`;
      const edge = edges.get(key);
      bits.push(edge && edge.color === 'red' ? 1 : 0);
    }
  }
  
  while (bits.length % 6 !== 0) bits.push(0);
  
  let payload = "";
  for (let i = 0; i < bits.length; i += 6) {
    const chunk = bits.slice(i, i + 6).reduce((acc, b) => (acc << 1) | b, 0);
    payload += String.fromCharCode(chunk + 63);
  }
  
  return header + payload;
}

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * Create a sorted key for an edge between two nodes.
 * Ensures consistent key regardless of order (0-1 === 1-0).
 * 
 * @param aId - First node ID
 * @param bId - Second node ID
 * @returns Sorted edge key string (e.g., "0-1")
 */
function sortedKey(aId: number, bId: number): string {
  return aId < bId ? `${aId}-${bId}` : `${bId}-${aId}`;
}

/**
 * Clamp a value between min and max (inclusive).
 * Used to keep nodes within canvas boundaries.
 */
function clamp(value: number, min: number, max: number): number {
  return Math.max(min, Math.min(max, value));
}

// ============================================================================
// Main Widget Component
// ============================================================================

/**
 * GraphWidget - Interactive graph drawing component for Lean infoview.
 * 
 * Props expected from Lean:
 * - graph6: string - Initial graph in graph6 format
 * - replaceRange: Lsp.Range | null - Document range to replace when sending back
 * 
 * RPC Methods called:
 * - graphWidget.updateGraph - Sends graph6 string back to Lean
 * 
 * @param props - Component props from Lean
 * @returns React element
 */
export default function(props) {
  // Get Lean contexts for RPC calls and editor interactions
  const rs = React.useContext(RpcContext);     // For calling Lean RPC methods
  const ec = React.useContext(EditorContext);   // For editing Lean documents
  
  const canvasRef = React.useRef<HTMLCanvasElement>(null);
  const [canvasSize, setCanvasSize] = React.useState({ width: 600, height: 400 });
  
  // Initialize graph state from props.graph6
  const initialGraph = parseGraph6(props.graph6 || "?", canvasSize.width, canvasSize.height);
  const [nodes, setNodes] = React.useState<Node[]>(initialGraph.nodes);
  const [edges, setEdges] = React.useState<Map<string, EdgeData>>(initialGraph.edges);
  const [status, setStatus] = React.useState("Ready");
  const [range, _] = React.useState(props.replaceRange);
  const [graphMode, setGraphMode] = React.useState<'simple' | 'colored'>('simple');
  
  // UI state for interaction
  const [selectedNodeId, setSelectedNodeId] = React.useState<number | null>(null);
  const [draggingNodeId, setDraggingNodeId] = React.useState<number | null>(null);
  const [dragOffset, setDragOffset] = React.useState({ x: 0, y: 0 });
  const [dragStart, setDragStart] = React.useState({ x: 0, y: 0 });
  const [isDragging, setIsDragging] = React.useState(false);
  
  // Compute graph6 string automatically whenever nodes or edges change
  const graph6String = React.useMemo(() => toGraph6(nodes, edges), [nodes, edges]);
  
  // Count red edges (the ones that will be exported)
  const edgeCount = React.useMemo(() => {
    let count = 0;
    edges.forEach(({ color }) => {
      if (color === 'red') count++;
    });
    return count;
  }, [edges]);
  
  // ============================================================================
  // Canvas Drawing
  // ============================================================================
  
  /**
   * Draw the entire graph on the canvas.
   * Called automatically when nodes, edges, or selection changes.
   */
  const draw = React.useCallback(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    
    const ctx = canvas.getContext('2d');
    if (!ctx) return;
    
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.save();
    
    // Draw edges
    ctx.lineWidth = 2;
    edges.forEach(({ color }, key) => {
      if (graphMode === 'simple' && color !== 'red') return;
      const [a, b] = key.split('-').map(Number);
      const na = nodes.find(n => n.id === a);
      const nb = nodes.find(n => n.id === b);
      if (!na || !nb) return;
      
      ctx.strokeStyle = color === 'blue' ? 'rgba(96, 165, 250, 0.85)' : 'rgba(248, 113, 113, 0.9)';
      ctx.beginPath();
      ctx.moveTo(na.x, na.y);
      ctx.lineTo(nb.x, nb.y);
      ctx.stroke();
    });
    
    // Draw nodes
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
      gradient.addColorStop(0, isSelected ? '#a5b4fc' : '#34d399');
      gradient.addColorStop(1, isSelected ? '#6366f1' : '#10b981');
      ctx.fillStyle = gradient;
      ctx.beginPath();
      ctx.arc(node.x, node.y, radius, 0, Math.PI * 2);
      ctx.fill();
      
      ctx.lineWidth = 2;
      ctx.strokeStyle = isSelected ? '#fef9c3' : 'rgba(255,255,255,0.6)';
      ctx.stroke();
      
      ctx.fillStyle = '#0b1224';
      ctx.font = 'bold 13px system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(index.toString(), node.x, node.y);
    });
    
    ctx.restore();
  }, [nodes, edges, selectedNodeId, graphMode]);
  
  // Redraw when dependencies change
  React.useEffect(() => {
    draw();
  }, [draw]);
  
  // ============================================================================
  // Graph Manipulation Functions
  // ============================================================================
  
  /**
   * Find the node at given canvas coordinates.
   * Returns undefined if no node is within the hit radius.
   */
  const findNodeAt = (x: number, y: number): Node | undefined => {
    const radius = 18;
    return nodes.find(node => {
      const dx = node.x - x;
      const dy = node.y - y;
      return Math.hypot(dx, dy) <= radius;
    });
  };
  
  /**
   * Add a new node at the specified canvas coordinates.
   * In colored mode, automatically connects to all existing nodes with blue edges.
   */
  const addNode = (x: number, y: number) => {
    const nextId = nodes.length > 0 ? Math.max(...nodes.map(n => n.id)) + 1 : 0;
    const newNode: Node = { id: nextId, x, y };
    setNodes(prev => [...prev, newNode]);
    
    if (graphMode === 'colored') {
      // Connect to all existing nodes as blue
      setEdges(prev => {
        const newEdges = new Map(prev);
        for (const existing of nodes) {
          const key = sortedKey(existing.id, newNode.id);
          newEdges.set(key, { color: 'blue' });
        }
        return newEdges;
      });
    }
    
    setStatus("Node added");
  };
  
  /**
   * Toggle an edge between two nodes.
   * 
   * In simple mode: adds or removes the edge.
   * In colored mode: toggles between red (connected) and blue (disconnected).
   */
  const toggleEdge = (aId: number, bId: number) => {
    if (aId === bId) return;
    const key = sortedKey(aId, bId);
    
    setEdges(prev => {
      const newEdges = new Map(prev);
      const existing = newEdges.get(key);
      
      if (graphMode === 'colored') {
        // Toggle red/blue
        if (!existing || existing.color === 'blue') {
          newEdges.set(key, { color: 'red' });
          setStatus(`Edge ${key} set to red (connected)`);
        } else {
          newEdges.set(key, { color: 'blue' });
          setStatus(`Edge ${key} set to blue (disconnected)`);
        }
      } else {
        // Add/remove red edges
        if (existing && existing.color === 'red') {
          newEdges.delete(key);
          setStatus(`Edge ${key} removed`);
        } else {
          newEdges.set(key, { color: 'red' });
          setStatus(`Edge ${key} added`);
        }
      }
      
      return newEdges;
    });
  };
  
  /**
   * Delete a node and all its incident edges.
   */
  const deleteNode = (nodeId: number) => {
    setNodes(prev => prev.filter(n => n.id !== nodeId));
    setEdges(prev => {
      const newEdges = new Map(prev);
      Array.from(newEdges.keys()).forEach(key => {
        const [a, b] = key.split('-').map(Number);
        if (a === nodeId || b === nodeId) newEdges.delete(key);
      });
      return newEdges;
    });
    
    if (selectedNodeId === nodeId) setSelectedNodeId(null);
    setStatus(`Node ${nodeId} deleted`);
  };
  
  // ============================================================================
  // Mouse Event Handlers
  // ============================================================================
  
  /**
   * Handle mouse down events on the canvas.
   * - Right-click: delete node
   * - Left-click on node: start dragging or selection
   */
  const handleMouseDown = (e: React.MouseEvent<HTMLCanvasElement>) => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    const x = (e.clientX - rect.left) * scaleX;
    const y = (e.clientY - rect.top) * scaleY;
    const node = findNodeAt(x, y);
    
    if (e.button === 2) {
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
  
  /**
   * Handle mouse move events - used for dragging nodes.
   * Applies coordinate scaling to handle CSS-scaled canvas.
   */
  const handleMouseMove = (e: React.MouseEvent<HTMLCanvasElement>) => {
    if (draggingNodeId === null) return;
    
    const canvas = canvasRef.current;
    if (!canvas) return;
    
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    const x = (e.clientX - rect.left) * scaleX;
    const y = (e.clientY - rect.top) * scaleY;
    
    const moved = Math.hypot(x - dragStart.x, y - dragStart.y) > 3;
    if (moved) setIsDragging(true);
    if (!isDragging && !moved) return;
    
    setNodes(prev => prev.map(node => {
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
  
  /**
   * Handle mouse up events - finalize drag or perform click action.
   * Click actions:
   * - First click: select node
   * - Second click: toggle edge between selected node and clicked node
   * - Click empty space: add new node
   */
  const handleMouseUp = (e: React.MouseEvent<HTMLCanvasElement>) => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    
    const rect = canvas.getBoundingClientRect();
    const scaleX = canvas.width / rect.width;
    const scaleY = canvas.height / rect.height;
    const x = (e.clientX - rect.left) * scaleX;
    const y = (e.clientY - rect.top) * scaleY;
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
  
  /**
   * Prevent context menu from showing on right-click.
   */
  const handleContextMenu = (e: React.MouseEvent<HTMLCanvasElement>) => {
    e.preventDefault();
  };
  
  // ============================================================================
  // Layout Algorithms
  // ============================================================================
  
  /**
   * Arrange nodes in a circle.
   * Useful for visualizing regular structures and cycles.
   */
  const applyCircleLayout = () => {
    const n = nodes.length;
    if (n === 0) return;
    
    const radius = Math.min(canvasSize.width, canvasSize.height) / 2 - 40;
    const cx = canvasSize.width / 2;
    const cy = canvasSize.height / 2;
    
    setNodes(prev => prev.map((node, i) => {
      const angle = (2 * Math.PI * i) / n;
      return {
        ...node,
        x: cx + radius * Math.cos(angle),
        y: cy + radius * Math.sin(angle)
      };
    }));
    
    setStatus("Applied circle layout");
  };
  
  /**
   * Apply force-directed layout using a spring model.
   * - All nodes repel each other (simulating charge)
   * - Red edges act as springs pulling nodes together
   * - Useful for finding natural graph layouts
   */
  const applySpringLayout = () => {
    const n = nodes.length;
    if (n === 0) return;
    
    const area = canvasSize.width * canvasSize.height;
    const k = Math.sqrt(area / (n + 0.001));
    let temperature = Math.min(canvasSize.width, canvasSize.height) / 8;
    const iterations = 250;
    
    let currentNodes = [...nodes];
    const idToIndex = new Map(currentNodes.map((node, i) => [node.id, i]));
    
    for (let iter = 0; iter < iterations; iter++) {
      const disp = currentNodes.map(() => ({ x: 0, y: 0 }));
      
      // Repulsive forces
      for (let i = 0; i < n; i++) {
        for (let j = i + 1; j < n; j++) {
          const dx = currentNodes[j].x - currentNodes[i].x;
          const dy = currentNodes[j].y - currentNodes[i].y;
          const dist = Math.hypot(dx, dy) + 0.01;
          const force = (k * k) / dist;
          const fx = (force * dx) / dist;
          const fy = (force * dy) / dist;
          disp[i].x -= fx;
          disp[i].y -= fy;
          disp[j].x += fx;
          disp[j].y += fy;
        }
      }
      
      // Attractive forces along red edges
      edges.forEach(({ color }, key) => {
        if (color !== 'red') return;
        const [aId, bId] = key.split('-').map(Number);
        const i = idToIndex.get(aId);
        const j = idToIndex.get(bId);
        if (i === undefined || j === undefined) return;
        
        const dx = currentNodes[j].x - currentNodes[i].x;
        const dy = currentNodes[j].y - currentNodes[i].y;
        const dist = Math.hypot(dx, dy) + 0.01;
        const force = (dist * dist) / k;
        const fx = (force * dx) / dist;
        const fy = (force * dy) / dist;
        disp[i].x += fx;
        disp[i].y += fy;
        disp[j].x -= fx;
        disp[j].y -= fy;
      });
      
      // Move nodes
      for (let i = 0; i < n; i++) {
        const dx = disp[i].x;
        const dy = disp[i].y;
        const dist = Math.hypot(dx, dy) || 1;
        const limited = Math.min(temperature, dist);
        currentNodes[i].x = clamp(
          currentNodes[i].x + (dx / dist) * limited,
          20,
          canvasSize.width - 20
        );
        currentNodes[i].y = clamp(
          currentNodes[i].y + (dy / dist) * limited,
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
  
  // ============================================================================
  // User Actions
  // ============================================================================
  
  /**
   * Clear all nodes and edges from the graph.
   */
  const clearGraph = () => {
    setNodes([]);
    setEdges(new Map());
    setSelectedNodeId(null);
    setStatus("Graph cleared");
  };
  
  /**
   * Send the current graph back to Lean via RPC.
   * 
   * This calls the Lean RPC method 'graphWidget.updateGraph' with:
   * - graph6: the current graph encoded as graph6 string
   * - replaceRange: the document range to replace (from props)
   * 
   * The Lean side should return:
   * - edit: DocumentEdit to apply
   * - newSelection: optional new cursor position
   * 
   * Example Lean implementation:
   * ```lean
   * @[server_rpc_method]
   * def graphWidget.updateGraph (params : GraphUpdateParams) : RequestM (RequestTask GraphUpdateResult) := do
   *   let edit := -- create edit to insert params.graph6 into document
   *   return { edit := edit, newSelection := none }
   * ```
   */
  const sendToLean = () => {
    setStatus("Sending to Lean...");
    rs.call('graphWidget.updateGraph', { 
      graph6: graph6String, 
      replaceRange: range 
    })
    .then(result => {
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
    })
    .catch(e => {
      console.error(mapRpcError(e));
      setStatus("Error sending to Lean");
    });
  };
  
  // ============================================================================
  // Export Functions
  // ============================================================================
  
  /**
   * Export graph as edge list format.
   * Format: one edge per line, "i j" where i and j are node indices.
   * Only exports red (connected) edges.
   */
  const exportEdgeList = () => {
    if (nodes.length === 0) return "";
    const idToIndex = new Map(nodes.map((n, i) => [n.id, i]));
    const lines: string[] = [];
    edges.forEach(({ color }, key) => {
      if (color !== 'red') return;
      const [a, b] = key.split('-').map(Number);
      const ia = idToIndex.get(a);
      const ib = idToIndex.get(b);
      if (ia !== undefined && ib !== undefined) {
        lines.push(`${ia} ${ib}`);
      }
    });
    return lines.join('\n');
  };
  
  /**
   * Export graph as adjacency matrix.
   * Format: n x n matrix where matrix[i][j] = 1 if edge exists, 0 otherwise.
   * Only exports red (connected) edges.
   */
  const exportAdjMatrix = () => {
    const n = nodes.length;
    const idToIndex = new Map(nodes.map((n, i) => [n.id, i]));
    const matrix = Array.from({ length: n }, () => Array(n).fill(0));
    edges.forEach(({ color }, key) => {
      if (color !== 'red') return;
      const [a, b] = key.split('-').map(Number);
      const i = idToIndex.get(a);
      const j = idToIndex.get(b);
      if (i !== undefined && j !== undefined) {
        matrix[i][j] = 1;
        matrix[j][i] = 1;
      }
    });
    return matrix.map(row => row.join(' ')).join('\n');
  };
  
  // ============================================================================
  // React Component Rendering
  // ============================================================================
  
  return e('div', { style: { 
    fontFamily: 'system-ui, sans-serif',
    background: '#0f172a',
    color: '#e2e8f0',
    borderRadius: '8px',
    overflow: 'hidden'
  } }, [
    // Header
    e('div', { style: { 
      padding: '12px 16px',
      background: 'rgba(15, 23, 42, 0.75)',
      borderBottom: '1px solid rgba(255, 255, 255, 0.08)'
    } }, [
      e('h3', { style: { margin: '0 0 8px 0', fontSize: '16px' } }, 'Graph Widget'),
      e('div', { style: { display: 'flex', gap: '8px', flexWrap: 'wrap', alignItems: 'center' } }, [
        e('span', { style: { 
          padding: '4px 8px',
          background: 'rgba(255, 255, 255, 0.08)',
          borderRadius: '999px',
          fontSize: '12px',
          border: '1px solid rgba(255, 255, 255, 0.15)'
        } }, `Nodes: ${nodes.length}`),
        e('span', { style: { 
          padding: '4px 8px',
          background: 'rgba(255, 255, 255, 0.08)',
          borderRadius: '999px',
          fontSize: '12px',
          border: '1px solid rgba(255, 255, 255, 0.15)'
        } }, `Edges: ${edgeCount}`),
        e('button', {
          onClick: () => setSelectedNodeId(null),
          style: {
            border: '1px solid rgba(255, 255, 255, 0.15)',
            background: 'rgba(255, 255, 255, 0.08)',
            color: 'inherit',
            padding: '6px 10px',
            borderRadius: '6px',
            cursor: 'pointer',
            fontSize: '12px'
          }
        }, 'Clear selection'),
        e('button', {
          onClick: clearGraph,
          style: {
            border: '1px solid rgba(239, 68, 68, 0.35)',
            background: 'rgba(239, 68, 68, 0.15)',
            color: '#fecdd3',
            padding: '6px 10px',
            borderRadius: '6px',
            cursor: 'pointer',
            fontSize: '12px'
          }
        }, 'Clear graph'),
        e('select', {
          value: graphMode,
          onChange: (ev: any) => setGraphMode(ev.target.value),
          style: {
            border: '1px solid rgba(255, 255, 255, 0.15)',
            background: 'rgba(255, 255, 255, 0.08)',
            color: 'inherit',
            padding: '6px 10px',
            borderRadius: '6px',
            fontSize: '12px',
            cursor: 'pointer'
          }
        }, [
          e('option', { value: 'simple' }, 'Simple graph'),
          e('option', { value: 'colored' }, 'Bi-colored graph')
        ]),
        e('button', {
          onClick: applyCircleLayout,
          style: {
            border: '1px solid rgba(255, 255, 255, 0.15)',
            background: 'rgba(255, 255, 255, 0.08)',
            color: 'inherit',
            padding: '6px 10px',
            borderRadius: '6px',
            cursor: 'pointer',
            fontSize: '12px'
          }
        }, 'Circle layout'),
        e('button', {
          onClick: applySpringLayout,
          style: {
            border: '1px solid rgba(255, 255, 255, 0.15)',
            background: 'rgba(255, 255, 255, 0.08)',
            color: 'inherit',
            padding: '6px 10px',
            borderRadius: '6px',
            cursor: 'pointer',
            fontSize: '12px'
          }
        }, 'Spring layout')
      ])
    ]),
    
    // Canvas
    e('canvas', {
      ref: canvasRef,
      width: canvasSize.width,
      height: canvasSize.height,
      onMouseDown: handleMouseDown,
      onMouseMove: handleMouseMove,
      onMouseUp: handleMouseUp,
      onContextMenu: handleContextMenu,
      style: {
        display: 'block',
        width: '100%',
        background: 'radial-gradient(circle at 50% 50%, rgba(255, 255, 255, 0.04), transparent 60%), #0b1224',
        cursor: 'crosshair'
      }
    }),
    
    // Bottom panel
    e('div', { style: { 
      padding: '12px 16px',
      background: 'rgba(10, 14, 26, 0.85)',
      borderTop: '1px solid rgba(255, 255, 255, 0.08)'
    } }, [
      e('div', { style: { 
        fontSize: '11px',
        color: '#cbd5e1',
        marginBottom: '8px'
      } }, 'Click empty space to add a node. Click two nodes to toggle edge. Drag to reposition. Right-click to delete.'),
      e('div', { style: { display: 'flex', gap: '8px', marginBottom: '8px', flexWrap: 'wrap' } }, [
        e('button', {
          onClick: sendToLean,
          style: {
            background: 'linear-gradient(135deg, #22d3ee, #6366f1)',
            color: '#0b1224',
            border: 'none',
            padding: '8px 16px',
            borderRadius: '6px',
            cursor: 'pointer',
            fontWeight: '600',
            fontSize: '13px'
          }
        }, '📤 Send to Lean'),
        e('button', {
          onClick: () => {
            navigator.clipboard.writeText(graph6String);
            setStatus('Copied graph6 to clipboard');
          },
          style: {
            border: '1px solid rgba(255, 255, 255, 0.15)',
            background: 'rgba(255, 255, 255, 0.08)',
            color: 'inherit',
            padding: '8px 12px',
            borderRadius: '6px',
            cursor: 'pointer',
            fontSize: '12px'
          }
        }, 'Copy graph6'),
        e('button', {
          onClick: () => {
            navigator.clipboard.writeText(exportEdgeList());
            setStatus('Copied edge list to clipboard');
          },
          style: {
            border: '1px solid rgba(255, 255, 255, 0.15)',
            background: 'rgba(255, 255, 255, 0.08)',
            color: 'inherit',
            padding: '8px 12px',
            borderRadius: '6px',
            cursor: 'pointer',
            fontSize: '12px'
          }
        }, 'Copy edges'),
        e('button', {
          onClick: () => {
            navigator.clipboard.writeText(exportAdjMatrix());
            setStatus('Copied adjacency matrix to clipboard');
          },
          style: {
            border: '1px solid rgba(255, 255, 255, 0.15)',
            background: 'rgba(255, 255, 255, 0.08)',
            color: 'inherit',
            padding: '8px 12px',
            borderRadius: '6px',
            cursor: 'pointer',
            fontSize: '12px'
          }
        }, 'Copy matrix')
      ]),
      e('div', { style: { 
        fontSize: '11px',
        fontFamily: 'monospace',
        color: '#94a3b8',
        wordBreak: 'break-all',
        marginBottom: '4px'
      } }, `graph6: ${graph6String}`),
      e('div', { style: { 
        fontSize: '11px',
        color: '#cbd5e1',
        fontStyle: 'italic'
      } }, status)
    ])
  ]);
}

