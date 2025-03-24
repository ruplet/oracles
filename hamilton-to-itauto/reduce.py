def get_ipc_formula_premises(adjacency_matrix):
    n = len(adjacency_matrix)
    premises = []

    # Helper to return a vertex variable at a given step.
    def v(vertex, step):
        # using 1-indexed vertex name for clarity
        return f"v_{vertex+1}_{step}"

    # Helper for the additional variable for closing condition.
    def v_prime(vertex):
        return f"v_{vertex+1}_prime_1"

    # (a) For every vertex, add initial premise (vₖ₁ → 1) → 0.
    for a in range(n):
        premises.append(f"({v(a,1)} → goal1) → goal0")

    # (b) For each step i = 2,..., n, for each vertex a and for every incoming edge (b,a)
    # add: vₐ₁ → ... → vₐᵢ₋₁ → v_bᵢ₋₁ → (vₐᵢ → (vₓᵢ for each x ≠ a, in order) → i) → i–1.
    for i in range(2, n+1):
        for a in range(n):
            for b in range(n):
                if a != b and adjacency_matrix[b][a] == 1:
                    antecedents = [v(a, j) for j in range(1, i)]  # vₐ₁, ..., vₐᵢ₋₁
                    antecedents.append(v(b, i-1))                   # then v_b, at step i-1
                    # For the consequent, list vₐᵢ and then all vₓᵢ for x ≠ a in increasing order.
                    consequent_vars = [v(a, i)]
                    consequent_vars.extend(v(x, i) for x in range(n) if x != a)
                    consequent = "(" + " → ".join(consequent_vars) + f" → goal{i})"
                    premise = " → ".join(antecedents) + " → " + consequent + f" → goal{i-1}"
                    premises.append(premise)

    # (c) For each edge (b,a) in E, add closing premise: v_bₙ → vₐ′₁ → n.
    for a in range(n):
        for b in range(n):
            if a != b and adjacency_matrix[b][a] == 1:
                premises.append(f"{v(b, n)} → {v_prime(a)} → goal{n}")
    return premises

def get_ipc_formula(adjacency_matrix):
    n = len(adjacency_matrix)
    premises = get_ipc_formula_premises(adjacency_matrix)
    # The overall IPC formula: n → (all premises) → 0.
    formula = f"{n} → " + " → ".join(premises) + " → goal0"
    return formula

def get_lean_file(formula, file_path, n):
    # Build a mapping to replace isolated numeric tokens with constant names.
    mapping = {"0": "zeroP"}
    for i in range(1, n):
        mapping[str(i)] = f"num{i}"
    mapping[str(n)] = "nP"
    # Replace tokens (splitting by ' → ')
    tokens = formula.split(" → ")
    new_tokens = []
    for token in tokens:
        if token in mapping:
            new_tokens.append(mapping[token])
        else:
            new_tokens.append(token)
    new_formula = " → ".join(new_tokens)
    
    # Generate declarations for vertex variables using 'variable' syntax.
    decls = []
    for a in range(n):
        for step in range(1, n+1):
            decls.append(f"variable (v_{a+1}_{step} : Prop)")
        decls.append(f"variable (v_{a+1}_prime_1 : Prop)")
        decls.append(f"variable (goal{a} : Prop)")
    decls.append(f"variable (goal{n} : Prop)")
    # Generate declarations for numeral constants using 'variable' syntax.
    decls.append("variable (zeroP : Prop)")
    for i in range(1, n):
        decls.append(f"variable (num{i} : Prop)")
    decls.append("variable (nP : Prop)")
    
    decl_block = "\n".join(decls)
    # Build the complete Lean file content with necessary imports.
    lean_file = f"""import Mathlib.Tactic.ITauto

-- filepath: {file_path}

/- Automatically generated Lean file for Hamilton cycle IPC formula -/

{decl_block}

theorem ipc_formula : 
  {new_formula} := 
by itauto

#print ipc_formula
"""
    return lean_file

if __name__ == '__main__':
    # Example graph: 3-cycle (edges: 0->1, 1->2, 2->0)
    adj_matrix_cycle = [[0, 1, 0],
                        [0, 0, 1],
                        [1, 0, 0]]
    formula_cycle = get_ipc_formula(adj_matrix_cycle)
    lean_file_cycle = get_lean_file(formula_cycle, "/home/maryjane/oracles/hamilton-to-itauto/output_cycle.lean", len(adj_matrix_cycle))
    # print("Lean file for the 3-cycle graph:")
    print(lean_file_cycle)

    import sys
    sys.exit()

    # Example graph: path (0->1, 1->2)
    adj_matrix_path = [[0, 1, 0],
                       [0, 0, 1],
                       [0, 0, 0]]
    formula_path = get_ipc_formula(adj_matrix_path)
    lean_file_path = get_lean_file(formula_path, "/home/maryjane/oracles/hamilton-to-itauto/output_path.lean", len(adj_matrix_path))
    print("\nLean file for the path graph:")
    print(lean_file_path)

    # Example graph: empty graph (no edges)
    adj_matrix_empty = [[0, 0, 0],
                        [0, 0, 0],
                        [0, 0, 0]]
    formula_empty = get_ipc_formula(adj_matrix_empty)
    lean_file_empty = get_lean_file(formula_empty, "/home/maryjane/oracles/hamilton-to-itauto/output_empty.lean", len(adj_matrix_empty))
    print("\nLean file for the empty graph:")
    print(lean_file_empty)