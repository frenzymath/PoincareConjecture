import PoincareConjecture.Proofs.M76.Wall.Mathlib.ExteriorHalfspaceChart
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_high_exterior_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L C R : Set X}
    (he : PLDomain e L) {h : X → ℝ} (hc : ContinuousOn h C) {beta : ℝ}
    (hR : R = (C \ interior L) ∩ {y | beta ≤ h y})
    {x : X} (hxL : x ∈ frontier L) (hxC : x ∈ interior C) (hxhigh : beta < h x) :
    ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3) (P : OpenPartialHomeomorph X V3),
      ell.contLinear v = 1 ∧ x ∈ P.source ∧ ell (P x) = 0 ∧
      (∀ i, (e i).symm.trans P ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ P.source, y ∈ R ↔ 0 ≤ ell (P y)) ∧
      P.source ⊆ interior (L ∪ R) ∧
      ∀ y ∈ P.source, y ∈ frontier R ↔ y ∈ frontier L := by
  let O := interior C ∩ h ⁻¹' Ioi beta
  have hO : IsOpen O :=
    (hc.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_Ioi
  have hxO : x ∈ O := ⟨hxC, hxhigh⟩
  obtain ⟨a, u, B, hau, hxB, haB, hB, hhalf⟩ := he.halfspace x hxL
  let P := B.restrOpen O hO
  have hPhalf : ∀ y ∈ P.source, y ∈ L ↔ 0 ≤ a (P y) :=
    fun y hy => hhalf y hy.1
  have hane : a.toAffineMap.linear ≠ 0 := by
    intro heq
    have hval : a.toAffineMap.linear u = 1 := hau
    rw [heq] at hval
    norm_num at hval
  have hanu : (-a).contLinear (-u) = 1 := by
    change -a.contLinear (-u) = 1
    rw [map_neg, neg_neg, hau]
  have hanne : (-a).toAffineMap.linear ≠ 0 := by
    change -a.toAffineMap.linear ≠ 0
    exact neg_ne_zero.mpr hane
  have hext := P.exterior_halfspace_and_frontier (fun y hy => hy.2.1) a hane hPhalf
  have hRhalf : ∀ y ∈ P.source, y ∈ R ↔ 0 ≤ (-a) (P y) := by
    intro y hy
    rw [hR]
    change (y ∈ C \ interior L ∧ beta ≤ h y) ↔ _
    exact (and_iff_left (show beta ≤ h y from le_of_lt hy.2.2)).trans (hext.1 y hy)
  have hOU : O ⊆ L ∪ R := by
    intro y hy
    by_cases hyL : y ∈ L
    · exact Or.inl hyL
    · apply Or.inr
      rw [hR]
      exact ⟨⟨interior_subset hy.1, fun hi => hyL (interior_subset hi)⟩,
        (show beta ≤ h y from le_of_lt hy.2)⟩
  have hOint : O ⊆ interior (L ∪ R) := interior_maximal hOU hO
  refine ⟨-a, -u, P, hanu, ⟨hxB, hxO⟩, ?_, ?_, hRhalf,
    (fun y hy => hOint hy.2), ?_⟩
  · change -a (B x) = 0
    rw [haB, neg_zero]
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right B (hB i) hO
  · intro y hy
    have hnew := (P.isImage_frontier_of_affine_nonneg (-a) hanne hRhalf).apply_mem_iff hy
    have hold := (P.isImage_frontier_of_affine_nonneg a hane hPhalf).apply_mem_iff hy
    change -a (P y) = 0 ↔ y ∈ frontier R at hnew
    change a (P y) = 0 ↔ y ∈ frontier L at hold
    exact hnew.symm.trans (neg_eq_zero.trans hold)

end PoincareConjecture.M76
