let nodes = [];
let connections = [];
let isDragging = false; // True if dragging a node
let isDrawing = false; // True if drawing an edge
let selectedNode = null; // Node being dragged or source node for edge
let tempEdge = null; // Temporary SVG line for edge drawing
let nodeCounter = 0; // Global counter for unique node IDs
let offsetX = 0; // Offset between mouse and node's top-left corner
let offsetY = 0; // Offset between mouse and node's top-left corner

const canvas = document.getElementById('canvas');
let initialCanvasWidth = canvas.clientWidth;
let initialCanvasHeight = canvas.clientHeight;

function createNode(type, x, y = 10) { // Default y-coordinate to 10
    const offset = 20; // Offset value in pixels
    let newX = x;
    let newY = y;

    // Check for overlapping nodes and add offset if necessary
    while (nodes.some(node => node.x === newX && node.y === newY)) {
        newX += offset;
        newY += offset;
    }

    const node = {
        id: `node-${nodeCounter++}`, // Use a counter to ensure unique IDs
        type: type,
        x: newX,
        y: newY,
        inputs: [],
        outputs: []
    };
    nodes.push(node);
    renderNode(node);
    blinkNode(node.id);
}

function renderNode(node) {
    const canvas = document.getElementById('canvas');
    const nodeElement = document.createElement('div');
    nodeElement.className = `node ${node.type}`;
    nodeElement.id = node.id; // Use the unique ID
    nodeElement.textContent = node.type.toUpperCase();
    nodeElement.style.left = `${node.x}px`;
    nodeElement.style.top = `${node.y}px`;
    nodeElement.style.opacity = 0.5;

    // Add event listeners
    nodeElement.addEventListener('mousedown', (e) => {
        if (e.ctrlKey) {
            // Ctrl + Click: Remove the node
            removeNode(node.id);
        } else if (e.shiftKey) {
            // Shift + Click: Start drawing an edge
            startEdgeDrawing(node);
        } else {
            // Normal Click: Start dragging the node
            startDragging(e, node);
        }
    });

    canvas.appendChild(nodeElement);
}

function removeNode(nodeId) {
    // Remove the node from the nodes array
    nodes = nodes.filter(node => node.id !== nodeId);

    // Remove all edges connected to the node
    connections = connections.filter(conn => conn.source !== nodeId && conn.target !== nodeId);

    // Remove the node from the DOM
    const nodeElement = document.getElementById(nodeId);
    if (nodeElement) {
        nodeElement.remove();
    }

    // Redraw all remaining edges
    redrawEdges();
}

// Remove an edge
function removeEdge(sourceId, targetId) {
    // Remove the edge from the connections array
    connections = connections.filter(conn => !(conn.source === sourceId && conn.target === targetId));

    // Redraw all remaining edges
    redrawEdges();
}

// Redraw all edges
function redrawEdges() {
    const svg = document.getElementById('edges');
    svg.innerHTML = ''; // Clear all edges

    // Re-add arrowhead marker definition to the SVG
    if (!document.getElementById('arrowhead')) {
        const defs = document.createElementNS('http://www.w3.org/2000/svg', 'defs');
        const marker = document.createElementNS('http://www.w3.org/2000/svg', 'marker');
        marker.setAttribute('id', 'arrowhead');
        marker.setAttribute('markerWidth', '10');
        marker.setAttribute('markerHeight', '7');
        marker.setAttribute('refX', '10');
        marker.setAttribute('refY', '3.5');
        marker.setAttribute('orient', 'auto');
        const arrowPath = document.createElementNS('http://www.w3.org/2000/svg', 'path');
        arrowPath.setAttribute('d', 'M0,0 L10,3.5 L0,7 Z');
        arrowPath.setAttribute('fill', '#007bff');
        marker.appendChild(arrowPath);
        defs.appendChild(marker);
        svg.appendChild(defs);
    }

    connections.forEach(conn => drawEdge(conn.source, conn.target));
}

function drawEdge(sourceId, targetId) {
    const svg = document.getElementById('edges');
    const sourceElement = document.getElementById(sourceId);
    const targetElement = document.getElementById(targetId);

    if (!sourceElement || !targetElement) {
        console.error('Source or target node not found!');
        return;
    }

    const sourceRect = sourceElement.getBoundingClientRect();
    const targetRect = targetElement.getBoundingClientRect();
    const sourceBorderRadius = parseFloat(window.getComputedStyle(sourceElement).borderRadius) || 0;
    const targetBorderRadius = parseFloat(window.getComputedStyle(targetElement).borderRadius) || 0;

    // Calculate the center points
    const sourceCenterX = sourceElement.offsetLeft + sourceRect.width / 2;
    const sourceCenterY = sourceElement.offsetTop + sourceRect.height / 2;
    const targetCenterX = targetElement.offsetLeft + targetRect.width / 2;
    const targetCenterY = targetElement.offsetTop + targetRect.height / 2;

    const sourceBounds = {
        left: sourceElement.offsetLeft,
        top: sourceElement.offsetTop,
        right: sourceElement.offsetLeft + sourceRect.width,
        bottom: sourceElement.offsetTop + sourceRect.height,
        borderRadius: sourceBorderRadius
    };

    const targetBounds = {
        left: targetElement.offsetLeft,
        top: targetElement.offsetTop,
        right: targetElement.offsetLeft + targetRect.width,
        bottom: targetElement.offsetTop + targetRect.height,
        borderRadius: targetBorderRadius
    };

    const intersectsSource = lineIntersectsRect(sourceCenterX, sourceCenterY, targetCenterX, targetCenterY, sourceBounds);
    const intersectsTarget = lineIntersectsRect(sourceCenterX, sourceCenterY, targetCenterX, targetCenterY, targetBounds);

    let startPoint = { x: sourceCenterX, y: sourceCenterY };
    let endPoint = { x: targetCenterX, y: targetCenterY };

    const sourceIntersection = getLineIntersectionWithRoundedRect(startPoint, endPoint, sourceBounds);
    if (sourceIntersection) {
        startPoint = sourceIntersection;
    }

    const targetIntersection = getLineIntersectionWithRoundedRect(endPoint, startPoint, targetBounds);
    if (targetIntersection) {
        endPoint = targetIntersection;
    }

    const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
    line.setAttribute('x1', startPoint.x);
    line.setAttribute('y1', startPoint.y);
    line.setAttribute('x2', endPoint.x);
    line.setAttribute('y2', endPoint.y);
    line.setAttribute('stroke-width', '2');
    line.setAttribute('marker-end', 'url(#arrowhead)');

    if (intersectsSource || intersectsTarget) {
        line.setAttribute('stroke', 'red');
    } else {
        line.setAttribute('stroke', '#007bff');
    }

    line.addEventListener('mousedown', (e) => {
        if (e.ctrlKey) {
            removeEdge(sourceId, targetId);
        }
    });
    svg.appendChild(line);
}

function getLineIntersectionWithRoundedRect(lineStart, lineEnd, rect) {
    const { left, top, right, bottom, borderRadius } = rect;
    const { x: x1, y: y1 } = lineStart;
    const { x: x2, y: y2 } = lineEnd;

    let closestIntersection = null;
    let minDistanceSq = Infinity;

    // Check intersection with straight edges
    const straightIntersection = getLineIntersectionWithRect(lineStart, lineEnd, { left, top, right, bottom });
    if (straightIntersection) {
        const dx = straightIntersection.x - lineStart.x;
        const dy = straightIntersection.y - lineStart.y;
        minDistanceSq = dx * dx + dy * dy;
        closestIntersection = straightIntersection;
    }

    // Check intersection with corner circles
    const corners = [
        { center: { x: left + borderRadius, y: top + borderRadius }, radius: borderRadius },    // Top-left
        { center: { x: right - borderRadius, y: top + borderRadius }, radius: borderRadius },   // Top-right
        { center: { x: right - borderRadius, y: bottom - borderRadius }, radius: borderRadius }, // Bottom-right
        { center: { x: left + borderRadius, y: bottom - borderRadius }, radius: borderRadius }  // Bottom-left
    ];

    for (const corner of corners) {
        const intersection = lineSegmentIntersectsCircle(lineStart, lineEnd, corner.center, corner.radius);
        if (intersection) {
            const dx = intersection.x - lineStart.x;
            const dy = intersection.y - lineStart.y;
            const distanceSq = dx * dx + dy * dy;
            if (distanceSq < minDistanceSq) {
                minDistanceSq = distanceSq;
                closestIntersection = intersection;
            }
        }
    }

    return closestIntersection;
}

function lineSegmentIntersectsCircle(p1, p2, center, radius) {
    const { x: x1, y: y1 } = p1;
    const { x: x2, y: y2 } = p2;
    const { x: cx, y: cy } = center;

    // Vector from center to p1
    const dx1 = x1 - cx;
    const dy1 = y1 - cy;

    // Vector along the line segment
    const dx = x2 - x1;
    const dy = y2 - y1;

    const a = dx * dx + dy * dy;
    const b = 2 * (dx1 * dx + dy1 * dy);
    const c = dx1 * dx1 + dy1 * dy1 - radius * radius;

    const discriminant = b * b - 4 * a * c;

    if (discriminant < 0) {
        return null; // No intersection
    }

    const t1 = (-b + Math.sqrt(discriminant)) / (2 * a);
    const t2 = (-b - Math.sqrt(discriminant)) / (2 * a);

    if ((t1 >= 0 && t1 <= 1) || (t2 >= 0 && t2 <= 1)) {
        // At least one intersection point is on the segment
        let intersectionPoint = null;
        let minDistSq = -1;

        if (t1 >= 0 && t1 <= 1) {
            const ix = x1 + t1 * dx;
            const iy = y1 + t1 * dy;
            const distSq = Math.pow(ix - x1, 2) + Math.pow(iy - y1, 2);
            if (distSq > minDistSq) {
                minDistSq = distSq;
                intersectionPoint = { x: ix, y: iy };
            }
        }

        if (t2 >= 0 && t2 <= 1) {
            const ix = x1 + t2 * dx;
            const iy = y1 + t2 * dy;
            const distSq = Math.pow(ix - x1, 2) + Math.pow(iy - y1, 2);
            if (distSq > minDistSq) {
                minDistSq = distSq;
                intersectionPoint = { x: ix, y: iy };
            }
        }
        return intersectionPoint;
    }

    return null; // Intersection(s) outside the segment
}

function getLineIntersectionWithRect(lineStart, lineEnd, rect) {
    const { left, top, right, bottom } = rect;
    const { x: x1, y: y1 } = lineStart;
    const { x: x2, y: y2 } = lineEnd;

    const lines = [
        { p1: { x: left, y: top }, p2: { x: right, y: top } },    // Top
        { p1: { x: right, y: top }, p2: { x: right, y: bottom } }, // Right
        { p1: { x: right, y: bottom }, p2: { x: left, y: bottom } }, // Bottom
        { p1: { x: left, y: bottom }, p2: { x: left, y: top } }     // Left
    ];

    let closestIntersection = null;
    let minDistanceSq = Infinity;

    for (const side of lines) {
        const intersection = getLineSegmentIntersection(lineStart, lineEnd, side.p1, side.p2);
        if (intersection) {
            const dx = intersection.x - lineStart.x;
            const dy = intersection.y - lineStart.y;
            const distanceSq = dx * dx + dy * dy;
            if (distanceSq < minDistanceSq) {
                minDistanceSq = distanceSq;
                closestIntersection = intersection;
            }
        }
    }

    return closestIntersection;
}

function getLineSegmentIntersection(p1, p2, p3, p4) {
    const det = (p2.x - p1.x) * (p4.y - p3.y) - (p2.y - p1.y) * (p4.x - p3.x);
    if (Math.abs(det) < 1e-9) {
        return null;
    }

    const t = ((p3.x - p1.x) * (p4.y - p3.y) - (p3.y - p1.y) * (p4.x - p3.x)) / det;
    const u = -((p2.x - p1.x) * (p3.y - p1.y) - (p2.y - p1.y) * (p3.x - p1.x)) / det;

    if (t >= 0 && t <= 1 && u >= 0 && u <= 1) {
        return {
            x: p1.x + t * (p2.x - p1.x),
            y: p1.y + t * (p2.y - p1.y)
        };
    }

    return null;
}

function lineIntersectsRect(x1, y1, x2, y2, rect) {
    // (Same as the version with tolerance from before)
    const tolerance = 1e-9;
    if ((x1 < rect.left - tolerance && x2 < rect.left - tolerance) || (x1 > rect.right + tolerance && x2 > rect.right + tolerance) ||
        (y1 < rect.top - tolerance && y2 < rect.top - tolerance) || (y1 > rect.bottom + tolerance && y2 > rect.bottom + tolerance)) {
        return false;
    }
    return intersectsLine(x1, y1, x2, y2, rect.left, rect.top, rect.right, rect.top) ||
           intersectsLine(x1, y1, x2, y2, rect.right, rect.top, rect.right, rect.bottom) ||
           intersectsLine(x1, y1, x2, y2, rect.right, rect.bottom, rect.left, rect.bottom) ||
           intersectsLine(x1, y1, x2, y2, rect.left, rect.bottom, rect.left, rect.top) ||
           (x1 >= rect.left - tolerance && x1 <= rect.right + tolerance && y1 >= rect.top - tolerance && y1 <= rect.bottom + tolerance) ||
           (x2 >= rect.left - tolerance && x2 <= rect.right + tolerance && y2 >= rect.top - tolerance && y2 <= rect.bottom + tolerance);
}

function intersectsLine(p1x, p1y, p2x, p2y, p3x, p3y, p4x, p4y) {
    const det = (p2x - p1x) * (p4y - p3y) - (p2y - p1y) * (p4x - p3x);
    const tolerance = 1e-9;
    if (Math.abs(det) < tolerance) {
        return false;
    }
    const t = ((p3x - p1x) * (p4y - p3y) - (p3y - p1y) * (p4x - p3x)) / det;
    const u = -((p2x - p1x) * (p3y - p1y) - (p2y - p1y) * (p3x - p1x)) / det;
    return t >= 0 - tolerance && t <= 1 + tolerance && u >= 0 - tolerance && u <= 1 + tolerance;
}

function createEdge(sourceId, targetId) {
    // Add the edge to the connections array
    connections.push({ source: sourceId, target: targetId });

    // Draw the edge on the canvas
    drawEdge(sourceId, targetId);
}

// Find the node at a specific position
function findNodeAtPosition(x, y) {
    const canvas = document.getElementById('canvas');
    const rect = canvas.getBoundingClientRect();

    // Calculate the mouse position relative to the canvas (no scroll offset)
    const mouseX = x - rect.left;
    const mouseY = y - rect.top;

    for (const node of nodes) {
        const nodeElement = document.getElementById(node.id);
        const nodeRect = nodeElement.getBoundingClientRect();
        if (
            mouseX >= nodeRect.left - rect.left &&
            mouseX <= nodeRect.right - rect.left &&
            mouseY >= nodeRect.top - rect.top &&
            mouseY <= nodeRect.bottom - rect.top
        ) {
            return node;
        }
    }
    return null;
}

// Handle mouse down
function handleMouseDown(e) {
    const canvas = document.getElementById('canvas');
    const rect = canvas.getBoundingClientRect();

    // Calculate the mouse position relative to the canvas (no scroll offset)
    const mouseX = e.clientX - rect.left;
    const mouseY = e.clientY - rect.top;

    if (e.ctrlKey) {
        // Ctrl + Click: Remove node or edge
        const node = findNodeAtPosition(e.clientX, e.clientY);
        if (node) {
            removeNode(node.id);
        } else {
            const edge = findEdgeAtPosition(e.clientX, e.clientY);
            if (edge) {
                removeEdge(edge.source, edge.target);
            }
        }
    } else if (e.shiftKey) {
        // Shift + Click: Start drawing an edge
        const node = findNodeAtPosition(e.clientX, e.clientY);
        if (node) {
            isDrawing = true;
            selectedNode = node;
            startEdgeDrawing(node);
        }
    } else {
        // Normal Click: Start dragging a node
        const node = findNodeAtPosition(e.clientX, e.clientY);
        if (node) {
            isDragging = true;
            selectedNode = node;
            startDragging(e, node);
        }
    }
}

function handleMouseMove(e) {
    if (isDragging && selectedNode) {
        // Get the canvas element and its bounding rectangle
        const canvas = document.getElementById('canvas');
        const rect = canvas.getBoundingClientRect();

        // Calculate the mouse position relative to the canvas (no scroll offset)
        let mouseX = e.clientX - rect.left;
        let mouseY = e.clientY - rect.top;

        // Get the node element and its dimensions
        const nodeElement = document.getElementById(selectedNode.id);
        const nodeRect = nodeElement.getBoundingClientRect();
        const nodeWidth = nodeRect.width;
        const nodeHeight = nodeRect.height;

        // Constrain the node's position within the canvas boundaries
        mouseX = Math.max(0, Math.min(mouseX - offsetX, rect.width - nodeWidth));
        mouseY = Math.max(0, Math.min(mouseY - offsetY, rect.height - nodeHeight));

        // Move the selected node
        selectedNode.x = mouseX;
        selectedNode.y = mouseY;
        nodeElement.style.left = `${selectedNode.x}px`;
        nodeElement.style.top = `${selectedNode.y}px`;

        // Redraw edges connected to the moved node
        redrawEdges();
    } else if (isDrawing && tempEdge) {
        // Update the temporary edge line
        const canvas = document.getElementById('canvas');
        const rect = canvas.getBoundingClientRect();
        const mouseX = e.clientX - rect.left;
        const mouseY = e.clientY - rect.top;
        tempEdge.setAttribute('x2', mouseX);
        tempEdge.setAttribute('y2', mouseY);
    }
}

// Handle mouse up
function handleMouseUp(e) {
    if (isDragging) {
        // Exit dragging mode
        isDragging = false;
        selectedNode = null;
    } else if (isDrawing) {
        // Exit drawing mode
        isDrawing = false;

        // Check if the mouse is over a target node
        const targetNode = findNodeAtPosition(e.clientX, e.clientY);
        if (targetNode && targetNode.id !== selectedNode.id) {
            // Create a directed edge
            createEdge(selectedNode.id, targetNode.id);
        }

        // Remove the temporary edge line
        if (tempEdge) {
            tempEdge.remove();
            tempEdge = null;
        }

        selectedNode = null;
    }
}

// Handle key down
function handleKeyDown(e) {
    if (e.key === 'Escape') {
        // Exit drawing or dragging mode
        isDragging = false;
        isDrawing = false;

        // Remove the temporary edge line
        if (tempEdge) {
            tempEdge.remove();
            tempEdge = null;
        }

        selectedNode = null;
    }
}

// Start dragging a node
function startDragging(e, node) {
    const nodeElement = document.getElementById(node.id);
    const nodeRect = nodeElement.getBoundingClientRect();
    const canvas = document.getElementById('canvas');
    const rect = canvas.getBoundingClientRect();

    // Calculate the offset between the mouse position and the node's top-left corner
    offsetX = e.clientX - nodeRect.left;
    offsetY = e.clientY - nodeRect.top;

    nodeElement.style.cursor = 'grabbing';
    document.body.classList.add('no-select'); // Disable text selection
    isDragging = true;
    selectedNode = node;
}

// Start drawing an edge
function startEdgeDrawing(node) {
    const svg = document.getElementById('edges');
    tempEdge = document.createElementNS('http://www.w3.org/2000/svg', 'line');
    tempEdge.classList.add('temp-edge');
    svg.appendChild(tempEdge);

    // Set the starting point of the line
    const sourceElement = document.getElementById(node.id);
    const sourceRect = sourceElement.getBoundingClientRect();
    const sourceX = sourceElement.offsetLeft + sourceRect.width / 2;
    const sourceY = sourceElement.offsetTop + sourceRect.height / 2;
    tempEdge.setAttribute('x1', sourceX);
    tempEdge.setAttribute('y1', sourceY);
    tempEdge.setAttribute('x2', sourceX);
    tempEdge.setAttribute('y2', sourceY);
    tempEdge.setAttribute('marker-end', 'url(#arrowhead)'); // Add arrowhead to temporary edge
}

// Blink animation for new nodes
function blinkNode(nodeId) {
    const nodeElement = document.getElementById(nodeId);
    nodeElement.classList.add('blink');
    setTimeout(() => nodeElement.classList.remove('blink'), 1000);
}

// Add event listeners for buttons
document.getElementById('add-input').addEventListener('click', () => createNode('input', 50));
document.getElementById('add-output').addEventListener('click', () => createNode('output', 50));
document.getElementById('add-and').addEventListener('click', () => createNode('and', 50));
document.getElementById('add-or').addEventListener('click', () => createNode('or', 50));
document.getElementById('add-not').addEventListener('click', () => createNode('not', 50));

// Export the circuit as JSON
document.getElementById('export-json').addEventListener('click', () => {
    const circuit = {
        nodes: nodes.map(node => ({
            id: node.id,
            type: node.type,
            x: node.x,
            y: node.y,
            inputs: node.inputs,
            outputs: node.outputs
        })),
        connections: connections
    };
    document.getElementById('output').textContent = JSON.stringify(circuit, null, 2);
});

// Add global event listeners
document.addEventListener('mousedown', handleMouseDown);
document.addEventListener('mousemove', handleMouseMove);
document.addEventListener('mouseup', handleMouseUp);
document.addEventListener('keydown', handleKeyDown);

function adjustNodePosition(node, originalX, originalY, nodeWidth, nodeHeight, canvasWidth, canvasHeight) {
    const tolerance = 3; // Tolerance value in pixels

    const atLeft = originalX <= tolerance;
    const atRight = originalX + nodeWidth >= initialCanvasWidth - tolerance;
    const atTop = originalY <= tolerance;
    const atBottom = originalY + nodeHeight >= initialCanvasHeight - tolerance;

    if (atLeft && atTop) {
        // Top-left corner
        node.x = 0;
        node.y = 0;
    } else if (atRight && atBottom) {
        // Bottom-right corner
        node.x = canvasWidth - nodeWidth;
        node.y = canvasHeight - nodeHeight;
    } else if (atLeft && atBottom) {
        // Bottom-left corner
        node.x = 0;
        node.y = canvasHeight - nodeHeight;
    } else if (atRight && atTop) {
        // Top-right corner
        node.x = canvasWidth - nodeWidth;
        node.y = 0;
    } else if (atTop) {
        // Top edge
        node.y = 0;
    } else if (atBottom) {
        // Bottom edge
        node.y = canvasHeight - nodeHeight;
    } else if (atLeft) {
        // Left edge
        node.x = 0;
    } else if (atRight) {
        // Right edge
        node.x = canvasWidth - nodeWidth;
    }

    // Ensure the node remains within the canvas boundaries
    node.x = Math.min(Math.max(node.x, 0), canvasWidth - nodeWidth);
    node.y = Math.min(Math.max(node.y, 0), canvasHeight - nodeHeight);
}

function resizeCanvas() {
    const newWidth = canvas.clientWidth;
    const newHeight = canvas.clientHeight;

    const widthScale = newWidth / initialCanvasWidth;
    const heightScale = newHeight / initialCanvasHeight;

    nodes.forEach(node => {
        const originalX = node.x;
        const originalY = node.y;

        node.x *= widthScale;
        node.y *= heightScale;

        const nodeElement = document.getElementById(node.id);
        const nodeWidth = nodeElement.offsetWidth;
        const nodeHeight = nodeElement.offsetHeight;

        adjustNodePosition(node, originalX, originalY, nodeWidth, nodeHeight, newWidth, newHeight);

        nodeElement.style.left = `${node.x}px`;
        nodeElement.style.top = `${node.y}px`;
    });

    initialCanvasWidth = newWidth;
    initialCanvasHeight = newHeight;

    redrawEdges();
}

// Add event listener for window resize
window.addEventListener('resize', resizeCanvas);

function findEdgeAtPosition(x, y) {
    const svg = document.getElementById('edges');
    const rect = svg.getBoundingClientRect();

    // Calculate the mouse position relative to the SVG (no scroll offset)
    const mouseX = x - rect.left;
    const mouseY = y - rect.top;

    for (const conn of connections) {
        const sourceElement = document.getElementById(conn.source);
        const targetElement = document.getElementById(conn.target);

        if (!sourceElement || !targetElement) continue;

        const sourceRect = sourceElement.getBoundingClientRect();
        const targetRect = targetElement.getBoundingClientRect();

        const sourceX = sourceElement.offsetLeft + sourceRect.width / 2;
        const sourceY = sourceElement.offsetTop + sourceRect.height / 2;
        const targetX = targetElement.offsetLeft + targetRect.width / 2;
        const targetY = targetElement.offsetTop + targetRect.height / 2;

        // Check if the mouse is close to the line
        const distance = Math.abs((targetY - sourceY) * mouseX - (targetX - sourceX) * mouseY + targetX * sourceY - targetY * sourceX) /
            Math.sqrt((targetY - sourceY) ** 2 + (targetX - sourceX) ** 2);

        if (distance < 5) { // Tolerance value in pixels
            return conn;
        }
    }
    return null;
}

// Add arrowhead marker definition to the SVG if it doesn't already exist
const svg = document.getElementById('edges');
if (!document.getElementById('arrowhead')) {
    const defs = document.createElementNS('http://www.w3.org/2000/svg', 'defs');
    const marker = document.createElementNS('http://www.w3.org/2000/svg', 'marker');
    marker.setAttribute('id', 'arrowhead');
    marker.setAttribute('markerWidth', '10');
    marker.setAttribute('markerHeight', '7');
    marker.setAttribute('refX', '10');
    marker.setAttribute('refY', '3.5');
    marker.setAttribute('orient', 'auto');
    const arrowPath = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    arrowPath.setAttribute('d', 'M0,0 L10,3.5 L0,7 Z');
    arrowPath.setAttribute('fill', '#007bff');
    marker.appendChild(arrowPath);
    defs.appendChild(marker);
    svg.appendChild(defs);
}