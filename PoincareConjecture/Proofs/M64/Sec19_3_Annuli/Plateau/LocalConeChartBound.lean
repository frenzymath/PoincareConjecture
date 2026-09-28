import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorEndpointBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture

variable {d n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64_euclidean_target_differential_bound_on_compact
    (g : RiemannianMetric n M) {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (f : EuclideanSpace ℝ (Fin d) → M)
    (hf : ∀ x ∈ K, ContMDiffAt (𝓡 d) (𝓡 n) 1 f x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin d),
      g.tangentNorm (f x) (mfderiv (𝓡 d) (𝓡 n) f x v) ≤ B * ‖v‖ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let J := (tangentBundleModelSpaceHomeomorph (𝓡 d)).symm
  let Q := K ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  have hQ : IsCompact Q := hK.prod (isCompact_closedBall _ _)
  have hc : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        g.tangentNorm (f p.1) (mfderiv (𝓡 d) (𝓡 n) f p.1 p.2)) Q := by
    intro p hp
    exact (Proofs.M58.continuous_bundle_norm.continuousAt.comp
      ((Proofs.M58.continuousAt_tangentMap_of_contMDiffAt (hf _ hp.1)).comp
        J.continuous.continuousAt)).continuousWithinAt
  obtain ⟨B, hB⟩ := hQ.exists_bound_of_continuousOn hc
  let C := max B 0
  have hunit (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ K)
      (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ ≤ 1) :
      g.tangentNorm (f x) (mfderiv (𝓡 d) (𝓡 n) f x v) ≤ C :=
    (le_abs_self _).trans ((hB (x, v) ⟨hx, by rwa [mem_closedBall_zero_iff]⟩).trans
      (le_max_left _ _))
  refine ⟨C, le_max_right _ _, ?_⟩
  intro x hx v
  by_cases hv : v = 0
  · subst v
    simp only [map_zero, RiemannianMetric.tangentNorm, map_zero, Real.sqrt_zero,
      norm_zero, mul_zero, le_refl]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvunit : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hvpos.ne']
  have hb := hunit x hx (‖v‖⁻¹ • v) hvunit
  change ‖mfderiv (𝓡 d) (𝓡 n) f x (‖v‖⁻¹ • v)‖ ≤ C at hb
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm] at hb
  have hm := mul_le_mul_of_nonneg_left hb hvpos.le
  rw [← mul_assoc, mul_inv_cancel₀ hvpos.ne', one_mul] at hm
  change ‖mfderiv (𝓡 d) (𝓡 n) f x v‖ ≤ C * ‖v‖
  simpa only [mul_comm] using hm

end PoincareConjecture
