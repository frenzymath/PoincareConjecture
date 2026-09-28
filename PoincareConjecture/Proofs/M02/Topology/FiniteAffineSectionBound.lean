import PoincareConjecture.Proofs.M02.Topology.FiniteAffineSection
import PoincareConjecture.Proofs.M02.Topology.FiniteConvexBall
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

open Set Metric

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

theorem minimal_affine_section_inverse_norm_le
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    (A : E →ᵃ[Real] F) (s : Finset E) (a : Real) (ha : 0 < a)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real F →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖)
    (hzero : ∃ x ∈ convexHull Real (s : Set E), A x = 0)
    (B : F ≃L[Real] (vectorSpan Real (s : Set E)))
    (hB : ∀ v : vectorSpan Real (s : Set E), B (A.linear v) = v) :
    ‖B.toContinuousLinearMap‖ ≤ diam (s : Set E) / a := by
  obtain ⟨x0, hx0, hAx0⟩ := hzero
  have hball := closedBall_subset_affine_convexHull_of_small_faces_gap
    A s a ha hgap ⟨x0, hx0, hAx0⟩
  have hbound (q : F) (hq : ‖q‖ ≤ a) : ‖B q‖ ≤ diam (s : Set E) := by
    obtain ⟨x, hx, hAx⟩ := hball (mem_closedBall_zero_iff.mpr hq)
    have hv : x - x0 ∈ vectorSpan Real (s : Set E) :=
      vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan
        (convexHull_subset_affineSpan _ hx) (convexHull_subset_affineSpan _ hx0)
    let v : vectorSpan Real (s : Set E) := ⟨x - x0, hv⟩
    have hAv : A.linear v = q := by
      change A.linear (x - x0) = q
      simpa only [vsub_eq_sub, hAx, hAx0, sub_zero] using A.linearMap_vsub x x0
    have hBq : B q = v := by
      rw [← hAv]
      exact hB v
    rw [hBq]
    change ‖x - x0‖ ≤ diam (s : Set E)
    have hd := dist_le_diam_of_mem
      (isBounded_convexHull.mpr s.finite_toSet.isBounded) hx hx0
    simpa only [convexHull_diam, dist_eq_norm] using hd
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg diam_nonneg ha.le)
  intro q hq
  change ‖B q‖ ≤ diam (s : Set E) / a
  have hqa : ‖a • q‖ ≤ a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hq, mul_one]
  have h := hbound (a • q) hqa
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at h
  exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using h)

theorem exists_bounded_minimal_affine_section_of_near_point
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    (A : E →ᵃ[Real] F) (s : Finset E) (a : Real) (ha : 0 < a)
    (hcard : s.card = Module.finrank Real F + 1)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real F →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖)
    (hnear : ∃ x ∈ convexHull Real (s : Set E), ‖A x‖ < a) :
    ∃ x ∈ convexHull Real (s : Set E), A x = 0 ∧
      ∃ B : F ≃L[Real] (vectorSpan Real (s : Set E)),
        (∀ z : F, A.linear (B z) = z) ∧
        (∀ v : vectorSpan Real (s : Set E), B (A.linear v) = v) ∧
        ‖B.toContinuousLinearMap‖ ≤ diam (s : Set E) / a := by
  obtain ⟨x, hx, hx0, B, hB1, hB2⟩ :=
    exists_minimal_affine_section_of_near_point A s a ha hcard hgap hnear
  exact ⟨x, hx, hx0, B, hB1, hB2,
    minimal_affine_section_inverse_norm_le A s a ha hgap ⟨x, hx, hx0⟩ B hB2⟩

end PoincareConjecture.Proofs.M02.Topology
