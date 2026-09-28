import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCurvatureCharts










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28




theorem exists_strongNeck_rescaled_curvature_bound :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∃ K : ℝ, 0 < K ∧
        ∀ (F : GeneralizedRicciFlowData.{u}) (t epsilon : ℝ)
          (S : GeneralizedStrongNeck F t epsilon)
          (H : RescaledRawCylinderData (C := F.slice t)
            (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
            (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S)),
          epsilon ≤ epsilon₀ → ∀ s ∈ Icc (-(1 / 2 : ℝ)) 0,
            ∀ x : strongNeckOpen S,
              (H.rescaling.flow.connection s).curvatureTensorNorm x ≤ K := by
  obtain ⟨epsilon₀, hepsilon₀, hthreshold, K, hK, hbound⟩ :=
    exists_half_cylinder_curvature_accuracy
  refine ⟨epsilon₀, hepsilon₀, hthreshold, K, hK, ?_⟩
  intro F t epsilon S H hsmall s hs x
  have hhalf : epsilon < 1 / 2 :=
    lt_of_le_of_lt (hsmall.trans hthreshold) (by norm_num)
  have hs' : s ∈ Ioc (-1 : ℝ) 0 := ⟨by linarith [hs.1], hs.2⟩
  let z := S.coordinate_inverse x.val
  have hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
    S.coordinate_inverse_mem x.val x.property
  have hpoint : strongNeckSourceMap S z = x := by
    apply Subtype.ext
    exact strongNeckSourceInverse_right S x
  have hnorm := hbound epsilon s S.epsilon_pos hsmall hs
    (roundCylinderPullback (H.rescaling.flow.metric s) (strongNeckSourceMap S))
    (GeneralizedStrongNeck.rescaled_source_comparison S H s hs') z hz
    (strongNeckCurvatureCoefficients S H hhalf s z.1 z.2)
    (strongNeckCurvatureCoefficients_contDiffAt S H hhalf s z.1 hz)
    (strongNeckCurvatureCoefficients_frozen_germ S H hhalf s z.1 hz)
  rw [strongNeckCurvatureCoefficients_norm_zero S H hhalf s z.1 hz] at hnorm
  change (H.rescaling.flow.connection s).curvatureTensorNorm (strongNeckSourceMap S z) ≤ K
    at hnorm
  simpa only [hpoint] using hnorm

end PoincareConjecture.M28
