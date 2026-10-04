import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Curvature.StrongNeckCurvatureBounds
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Geometry.StrongNeckHalfFlow
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Geometry.StrongNeckShiBounds

/-!
# Actual source curvature derivatives on the closed quarter window

Theorem 3.28, Morgan--Tian p. 51, and Proposition 5.14, pp. 90-91.
The original strong-neck comparison gives curvature on its whole backward
half-window. The terminal neck then constructs the initial compact balls
needed for all derivative orders, uniformly through time zero. Every
constant precedes the original source and its once-chosen rescaling.
See the source-quarter-window-derivatives derivation under cap-topology.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28

/-- Original strong-neck data produce whole-source half-window curvature
and all spatial covariant curvature derivatives on the closed quarter
window, measured on the fixed terminal center ball. No curvature,
derivative or compact-collar bound is an input (Theorem 3.28, p. 51). -/
theorem exists_strongNeck_source_quarter_bounds_accuracy
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
              ∀ m : ℕ, ∀ s ∈ Icc (-(1 / 4 : ℝ)) 0,
                ∀ q ∈ (G.metric 0).ball (strongNeckSourceCenter S) (epsilon⁻¹ / 16),
                  (G.connection s).curvatureDerivativeNorm m q ≤ B m := by
  classical
  obtain ⟨epsilon₀, hepsilon₀, hthreshold, K, hK, hcurvature⟩ :=
    exists_strongNeck_rescaled_curvature_bound.{u}
  refine ⟨epsilon₀, hepsilon₀, hthreshold, K, hK, ?_⟩
  intro epsilon hepsilon hsmall
  choose B hB hderiv using
    fun m => exists_source_neck_quarter_derivative_bound hShi hepsilon hK m
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
  intro m s hs q hq
  exact hderiv m (strongNeckOpen S) G N rfl rfl hRm s hs q hq

end PoincareMT.M28
