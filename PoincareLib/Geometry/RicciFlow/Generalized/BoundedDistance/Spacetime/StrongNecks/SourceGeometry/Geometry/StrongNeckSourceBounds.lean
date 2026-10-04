import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Curvature.StrongNeckCurvatureBounds
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Geometry.StrongNeckHalfFlow
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.StrongNecks.Geometry.StrongNeckShiBounds

/-!
# Actual curvature bounds for every normalized source index

Theorem 3.28, Morgan--Tian p. 51, and Proposition 5.14, pp. 90-91.
The original strong-neck comparison supplies the whole half-window bound;
the local Shi application constructs all terminal derivative bounds.
The constants precede every source flow and its chosen rescaling. This
fills the analytic source-family inputs of M28 derivations 32 and 33.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28

/-- Original strong-neck data produce uniform half-window curvature and
all terminal derivative bounds, with no curvature hypothesis supplied by
the source family; Theorem 3.28 and Proposition 5.14, pp. 51, 90-91. -/
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

end PoincareMT.M28
