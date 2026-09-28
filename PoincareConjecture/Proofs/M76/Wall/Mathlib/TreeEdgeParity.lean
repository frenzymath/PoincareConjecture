import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two









set_option autoImplicit false

namespace SimpleGraph



theorem IsTree.exists_edge_parity {V : Type*} {D : SimpleGraph V}
    (hD : D.IsTree) (root : V) (weight : Sym2 V → ZMod 2) :
    ∃ sigma : V → ZMod 2, sigma root = 0 ∧
      ∀ {u v : V}, D.Adj u v → sigma u + sigma v = weight s(u, v) := by
  classical
  choose p hp using fun v => (hD.existsUnique_path root v).exists
  let sigma : V → ZMod 2 := fun v => ((p v).edges.map weight).sum
  have hroot : p root = .nil :=
    (hD.existsUnique_path root root).unique (hp root) Walk.IsPath.nil
  refine ⟨sigma, ?_, ?_⟩
  · simp [sigma, hroot]
  · intro u v huv
    by_cases hu : u ∈ (p v).support
    · have hpath : p v = (p u).concat huv :=
        hD.isAcyclic.path_concat (hp u) (hp v) huv hu
      have hsum : sigma v = sigma u + weight s(u, v) := by
        simp [sigma, hpath]
      rw [hsum]
      exact CharTwo.add_cancel_left _ _
    · have hpath : p u = (p v).concat huv.symm :=
        (hD.existsUnique_path root u).unique (hp u) ((hp v).concat hu huv.symm)
      have hsum : sigma u = sigma v + weight s(v, u) := by
        simp [sigma, hpath]
      calc
        sigma u + sigma v = (sigma v + weight s(u, v)) + sigma v := by
          rw [hsum, Sym2.eq_swap (a := v) (b := u)]
        _ = (sigma v + sigma v) + weight s(u, v) := by ac_rfl
        _ = weight s(u, v) := by rw [CharTwo.add_self_eq_zero, zero_add]

end SimpleGraph
