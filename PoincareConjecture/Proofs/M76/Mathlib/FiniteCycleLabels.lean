import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fin.Basic

set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V : Type*} [Finite V]

theorem exists_cyclic_labels_of_two_neighbors (G : SimpleGraph V) (hc : G.Connected)
    (hdegree : ∀ v, (G.neighborSet v).ncard = 2) :
    ∃ (n : ℕ) (e : Fin (n + 3) ≃ V), ∀ x y,
      G.Adj x y ↔ ∃ i, (e i = x ∧ e (i + 1) = y) ∨
        (e i = y ∧ e (i + 1) = x) := by
  classical
  let := Fintype.ofFinite V
  let := hc.nonempty
  let a : V := Classical.arbitrary V
  have hcycles : G.IsCycles := fun {v} _ => hdegree v
  have ha : (G.neighborSet a).Nonempty :=
    nonempty_of_ncard_ne_zero (by rw [hdegree]; norm_num)
  obtain ⟨p, hp, hvertices⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := G.connectedComponentMk a) (show a ∈ (G.connectedComponentMk a).supp from rfl) ha
  have hall : ∀ x, x ∈ p.toSubgraph.verts := by
    intro x
    rw [hvertices, ConnectedComponent.mem_supp_iff]
    exact ConnectedComponent.sound (hc x a)
  let n := p.length - 3
  have hlength : n + 3 = p.length := Nat.sub_add_cancel hp.three_le_length
  let v : Fin (n + 3) → V := fun i => p.getVert i.val
  have hvinj : Function.Injective v := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val ≤ p.length - 1; omega)
      (by change j.val ≤ p.length - 1; omega) hij
  have hvsurj : Function.Surjective v := by
    intro x
    obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp
      (p.mem_verts_toSubgraph.mp (hall x))
    by_cases hilt : i < p.length
    · exact ⟨⟨i, by omega⟩, hi⟩
    · have hieq : i = p.length := by omega
      have hax : a = x := by simpa only [hieq, Walk.getVert_length] using hi
      exact ⟨0, (p.getVert_zero).trans hax⟩
  have hnext : ∀ i : Fin (n + 3), v (i + 1) = p.getVert (i.val + 1) := by
    intro i
    by_cases hi : i.val + 1 < n + 3
    · change p.getVert (i + 1).val = p.getVert (i.val + 1)
      rw [Fin.val_add_one_of_lt' hi]
    · have he : i.val + 1 = p.length := by omega
      have hzero : i + 1 = 0 := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one, Fin.val_zero]
        rw [he, ← hlength, Nat.mod_self]
      rw [hzero, he, Walk.getVert_length]
      exact p.getVert_zero
  let e : Fin (n + 3) ≃ V := Equiv.ofBijective v ⟨hvinj, hvsurj⟩
  refine ⟨n, e, ?_⟩
  intro x y
  rw [← hp.adj_toSubgraph_iff_of_isCycles hcycles (hall x) y, p.toSubgraph_adj_iff]
  constructor
  · rintro ⟨i, hi, hil⟩
    refine ⟨⟨i, by omega⟩, ?_⟩
    change (v ⟨i, by omega⟩ = x ∧ v (⟨i, by omega⟩ + 1) = y) ∨
      (v ⟨i, by omega⟩ = y ∧ v (⟨i, by omega⟩ + 1) = x)
    rw [hnext]
    exact Sym2.eq_iff.mp hi
  · rintro ⟨i, hi⟩
    refine ⟨i.val, ?_, by omega⟩
    apply Sym2.eq_iff.mpr
    change (v i = x ∧ v (i + 1) = y) ∨ (v i = y ∧ v (i + 1) = x) at hi
    rwa [hnext] at hi

end SimpleGraph
