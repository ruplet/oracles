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
    connections.forEach(conn => drawEdge(conn.source, conn.target));
}

// Draw a permanent edge on the canvas
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

    const sourceX = sourceElement.offsetLeft + sourceRect.width / 2;
    const sourceY = sourceElement.offsetTop + sourceRect.height / 2;
    const targetX = targetElement.offsetLeft + targetRect.width / 2;
    const targetY = targetElement.offsetTop + targetRect.height / 2;

    const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
    line.setAttribute('x1', sourceX);
    line.setAttribute('y1', sourceY);
    line.setAttribute('x2', targetX);
    line.setAttribute('y2', targetY);
    line.setAttribute('stroke', '#007bff');
    line.setAttribute('stroke-width', '2');
    svg.appendChild(line);
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
        if (node) removeNode(node.id);
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