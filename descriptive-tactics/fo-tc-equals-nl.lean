-- import Std.Data.List.Basic
-- import Std.Tactic.Basic

-- Type for nodes
inductive Node where
  | n0 : Node
  | n1 : Node
  | n2 : Node
  deriving DecidableEq

-- Type for edges
def Edge := Node × Node

-- Type for a graph
def Graph := List Edge

-- Example graph
def my_graph : Graph := [(Node.n0, Node.n1), (Node.n1, Node.n2)]

-- Inductive definition of reachability
inductive Reachable (g : Graph) : Node → Node → Prop where
  | direct_edge : (start, end) ∈ g → Reachable g start end
  | step : ∀ (intermediate : Node),
           Reachable g start intermediate →
           Reachable g intermediate end →
           Reachable g start end

-- Theorem: n2 is reachable from n0 in my_graph
theorem n0_reachable_n2 : Reachable my_graph Node.n0 Node.n2 := by
  apply Reachable.step with Node.n1
  · apply Reachable.direct_edge
    simp [my_graph]
  · apply Reachable.direct_edge
    simp [my_graph]

-- **Model:**
-- The model is defined by `my_graph`.
-- - Domain: The set of nodes `{Node.n0, Node.n1, Node.n2}`.
-- - Binary Relation (Edges): The relation `E(x, y)` holds if the pair `(x, y)` is in `my_graph`.
--   So, `E(Node.n0, Node.n1)` is true, and `E(Node.n1, Node.n2)` is true.

-- **Reduction to FO[TC] Formula:**
-- The theorem `n0_reachable_n2` is about reachability between the specific nodes `Node.n0` and `Node.n2` in the specific graph `my_graph`.
-- We can express this using an FO[TC] formula. Let the edge relation be represented by `E(x, y)`.
-- The formula for reachability from `Node.n0` to `Node.n2` using the transitive closure of `E` is:

-- `[TC_{u,v} E(u, v)](Node.n0, Node.n2)`

-- Where:
-- - `TC_{u,v}` denotes the transitive closure operator applied to the binary relation defined by `E(u, v)`.
-- - `Node.n0` and `Node.n2` are constants representing the nodes.

-- **Explanation of the Reduction:**
-- The Lean theorem `n0_reachable_n2` is proven by showing a path from `Node.n0` to `Node.n2` within `my_graph` based on the rules of the `Reachable` predicate. The proof explicitly uses the edge `(Node.n0, Node.n1)` and then the edge `(Node.n1, Node.n2)`.

-- The FO[TC] formula `[TC_{u,v} E(u, v)](Node.n0, Node.n2)` is true in the model defined by `my_graph` if and only if there exists a path from `Node.n0` to `Node.n2` using the edge relation `E`.

-- - The Lean proof demonstrates the existence of this path.
-- - The FO[TC] formula asserts the existence of such a path.

-- Therefore, proving the Lean theorem `n0_reachable_n2` is equivalent to showing that the FO[TC] formula `[TC_{u,v} E(u, v)](Node.n0, Node.n2)` is true in the model defined by `my_graph`.

-- **How to Compute the Model and Formula:**
-- 1. **Identify the specific instance:** The Lean theorem focuses on `my_graph` and the nodes `Node.n0` and `Node.n2`.
-- 2. **Define the domain of the model:** The domain is the set of nodes involved: `{Node.n0, Node.n1, Node.n2}`. In Lean, this is given by the `Node` inductive type and the specific instances.
-- 3. **Define the base relations:** The `my_graph` definition provides the edge relation `E(x, y)` which holds if `(x, y)` is in the list. In Lean, `(x, y) ∈ my_graph`.
-- 4. **Construct the FO[TC] formula:** Use the transitive closure operator on the edge relation, applied to the specific start and end nodes from the theorem.

-- **Non-Triviality:**
-- While this example is simple, it illustrates the basic principle. More complex theorems about graphs, orderings, or other relational structures that can be proven in Lean often have corresponding representations as FO[TC] formulas in appropriate models. The FO[TC]=NL theorem connects the truth of these formulas in finite models to the complexity class NL.
