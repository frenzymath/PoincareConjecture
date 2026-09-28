import PoincareConjecture.Proofs.M28.Generalized.StrongNeckCurvatureBounds
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckHalfFlow
import PoincareConjecture.Proofs.M28.Generalized.StrongNeckShiBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

theorem exists_strongNeck_source_bounds_accuracy
    (hShi : LocalCurvatureDerivativeEstimates.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∃ K : ℝ, 0 < K ∧
        ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
          ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
            ∀ (F : GeneralizedRicciFlowData.{u}) (t : ℝ)
              (S : GeneralizedStrongNeck F t epsilon)
              (H : RescaledRawCylinderData (C := F.slice t)
                (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
                (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S)),
              let G := GeneralizedStrongNeck.rescaled_half_flow S H
              (∀ s ∈ Icc (-(1 / 2 : ℝ)) 0, ∀ x : strongNeckOpen S,
                (G.connection s).curvatureTensorNorm x ≤ K) ∧
              ∀ m : ℕ, ∀ q ∈ (G.metric 0).ball (strongNeckSourceCenter S)
                (epsilon⁻¹ / 16), (G.connection 0).curvatureDerivativeNorm m q ≤ B m := by
  classical
  obtain ⟨epsilon₀, hepsilon₀, hthreshold, K, hK, hcurvature⟩ :=
    exists_strongNeck_rescaled_curvature_bound.{u}
  refine ⟨epsilon₀, hepsilon₀, hthreshold, K, hK, ?_⟩
  intro epsilon hepsilon hsmall
  choose B hB hderiv using
    fun m => exists_source_neck_terminal_derivative_bound hShi hepsilon hK m
  refine ⟨B, hB, ?_⟩
  intro F t S H
  let G := GeneralizedStrongNeck.rescaled_half_flow S H
  have hRm : ∀ s ∈ Icc (-(1 / 2 : ℝ)) 0, ∀ x : strongNeckOpen S,
      (G.connection s).curvatureTensorNorm x ≤ K :=
    hcurvature F t epsilon S H hsmall
  refine ⟨hRm, ?_⟩
  have hhalf : epsilon < 1 / 2 :=
    lt_of_le_of_lt (hsmall.trans hthreshold) (by norm_num)
  let N := GeneralizedStrongNeck.rescaled_half_source_neck S H hhalf
  intro m q hq
  exact hderiv m (strongNeckOpen S) G N rfl rfl hRm q hq

end PoincareConjecture.M28
