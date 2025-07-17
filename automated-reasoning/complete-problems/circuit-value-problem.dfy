include "DafnyProjects/TopologicalSorting.dfy"

datatype GateType = AND | OR | NOT | INPUT
datatype Circuit = Circuit(
    graph: Graph<(nat)>,
    gateTypes: map<(nat), GateType>,
    inputs: set<(nat)>,
    outputs: set<(nat)>
)

ghost predicate validCircuit(c: Circuit)
{
    acyclic(c.graph)
    && validGraph(c.graph)
    && (forall v :: (v in c.inputs ==> v in c.graph.V))
    && (forall v :: (v in c.outputs ==> v in c.graph.V))
    && (forall v :: (v in c.inputs ==> !hasIncomingEdges(c.graph, v)))
    && (forall v :: (v in c.outputs ==> !hasOutcomingEdges(c.graph, v)))
    && (forall v :: (v in c.graph.V && !hasIncomingEdges(c.graph, v) ==> v in c.inputs))
    && (forall v :: (v in c.graph.V && !hasOutcomingEdges(c.graph, v) ==> v in c.outputs))
    && (forall v :: (v in c.graph.V ==> v in c.gateTypes.Keys))
    && (forall v :: (v in c.graph.V && c.gateTypes[v] == INPUT ==> v in c.inputs))
    && (forall v :: (v in c.graph.V && c.gateTypes[v] == NOT ==> inDegree(c.graph, v) == 1))
    && (forall v :: (v in c.graph.V && c.gateTypes[v] == AND ==> inDegree(c.graph, v) == 2))
    && (forall v :: (v in c.graph.V && c.gateTypes[v] == OR ==> inDegree(c.graph, v) == 2))
}

// seq to set and back: https://stackoverflow.com/questions/62962130/how-to-prove-that-turning-a-set-into-a-sequence-and-back-is-an-identity-in-dafny
method getCircuitInNodes(c: Circuit)
    returns (result: map<nat, set<nat>>)
    requires validCircuit(c)
    ensures forall i :: i in c.graph.V ==> i in result.Keys
    ensures forall i :: i in result.Keys ==> i in c.graph.V
    ensures forall i :: i in c.graph.V ==> result[i] == (set v | v in c.graph.V && (i, v) in c.graph.E)
{
    var work : array<set<nat>> := new set<nat>[|c.graph.V|];
    var nodes := c.graph.V;
    for i := 0 to |nodes| - 1
    {
        var node :| node in nodes;
        work[node] := set v | v in c.graph.V && (node, v) in c.graph.E;
        nodes := nodes - {node};
    }
}


method {:noVerify} circuitValue(c: Circuit, inputs: map<nat, bool>) returns (values: map<nat, bool>)
    requires validCircuit(c)
    requires forall i :: i in c.inputs ==> i in inputs.Keys
    requires forall i :: i in inputs.Keys ==> i in c.inputs
    ensures forall i :: i in c.outputs ==> i in values.Keys
    ensures forall i :: i in values.Keys ==> i in c.outputs
{
    var nodeValues: array<bool> := new bool[|c.graph.V|];
    var topOrder := topsort(c.graph);
    var requirements := getCircuitInNodes(c);
    
    for i := 0 to |topOrder| - 1
    {
        var node : nat := topOrder[i];
        if c.gateTypes[node] == INPUT {
            nodeValues[node] := inputs[node];
        } else if c.gateTypes[node] == NOT {
            var inputNode :| inputNode in requirements[node]
            nodeValues[node] := !nodeValues[inputNode];
        } else if c.gateTypes[node] == AND {
            var inputNode1 := requirements[node].E[0].1;
            var inputNode2 := requirements[node].E[1].1;
            nodeValues[node] := nodeValues[inputNode1] && nodeValues[inputNode2];
        } else if c.gateTypes[node] == OR {
            var inputNode1 := requirements[node].E[0].1;
            var inputNode2 := requirements[node].E[1].1;
            nodeValues[node] := nodeValues[inputNode1] || nodeValues[inputNode2];
        }
    }
}