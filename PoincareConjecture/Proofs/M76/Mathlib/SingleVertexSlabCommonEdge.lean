import PoincareConjecture.Proofs.M76.Mathlib.RegularTriangleIntersection
import PoincareConjecture.Proofs.M76.Mathlib.AffineEdgeSlab

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem common_edge_of_singleVertexSlab_intersection (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {α β : ℝ} {q : E}
    (hreg : ∀ z ∈ K.vertices, A z ∈ Icc α β → z = q)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hsc : s.card = 3) (htc : t.card = 3) (hne : s ≠ t) {x : E}
    (hxs : x ∈ convexHull ℝ (s : Set E)) (hxt : x ∈ convexHull ℝ (t : Set E))
    (hxA : A x ∈ Icc α β) (hxq : x ≠ q) :
    ∃ e : Finset E, e.card = 2 ∧ e ∈ K.faces ∧ e ⊆ s ∧ e ⊆ t ∧
      x ∈ convexHull ℝ (e : Set E) ∧ InjOn A (convexHull ℝ (e : Set E)) := by
  classical
  have hx : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨hxs, hxt⟩
  have hvertex (z : E) (hz : z ∈ s ∩ t) : z ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp hz).1)
      (Finset.singleton_nonempty z)
  have hneinter : s ∩ t ≠ s := fun heq => hne
    (Finset.eq_of_subset_of_card_le (heq ▸ Finset.inter_subset_right) (by omega))
  have hhi := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hneinter⟩)
  have hpos := (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hx⟩)).card_pos
  have hnotone : (s ∩ t).card ≠ 1 := by
    intro hcard
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hzmem : z ∈ s ∩ t := by rw [hz]; exact Finset.mem_singleton_self z
    have hxz : x = z := by simpa only [hz, Finset.coe_singleton, convexHull_singleton,
      mem_singleton_iff] using hx
    exact hxq (hxz.trans (hreg z (hvertex z hzmem) (hxz ▸ hxA)))
  have hcard : (s ∩ t).card = 2 := by omega
  refine ⟨s ∩ t, hcard, K.down_closed hs Finset.inter_subset_left
    (Finset.card_pos.mp hpos), Finset.inter_subset_left, Finset.inter_subset_right, hx, ?_⟩
  obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp hcard
  have hamem : a ∈ s ∩ t := by rw [heq]; simp
  have hbmem : b ∈ s ∩ t := by rw [heq]; simp
  have hba : A b ≠ A a := by
    intro hequal
    have hconstant : convexHull ℝ ({a, b} : Set E) ⊆ {y | A y = A a} := by
      apply convexHull_min ?_ ((convex_singleton (A a)).affine_preimage A)
      intro y hy
      rcases hy with rfl | rfl
      · rfl
      · exact hequal
    have hxa : A x = A a := hconstant (by simpa only [heq, Finset.coe_pair] using hx)
    have haA : A a ∈ Icc α β := hxa ▸ hxA
    have hbA : A b ∈ Icc α β := hequal.symm ▸ haA
    exact hab ((hreg a (hvertex a hamem) haA).trans (hreg b (hvertex b hbmem) hbA).symm)
  rw [heq, Finset.coe_pair]
  exact (A.injOn_edgeLine hba).mono (convexHull_subset_affineSpan _)

end Geometry.SimplicialComplex
