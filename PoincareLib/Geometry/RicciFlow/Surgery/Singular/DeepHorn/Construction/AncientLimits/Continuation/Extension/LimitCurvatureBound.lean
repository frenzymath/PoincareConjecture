import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Continuation.Extension.LimitScalarBound
import PoincareLib.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareLib.Geometry.Riemannian.Curvature.Scalar.SharpBounds

/-!
# A uniform all-time curvature bound on the actual retained limit

Morgan--Tian Claim 11.35 and its ancient-limit continuation, printed
pp. 289-291. Nonnegative curvature gives the sharp full-norm bound by
scalar curvature for the actual connection. Cofinal source cylinders
therefore give one bound on every included limit slice.
Reviewed derivation: `claim11_35-stage-controls-and-limit-bound.md`, section 5.
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

/-- The one common source scalar bound controls full curvature at every
time of the same actual limit. Source: the final ancient-limit argument
after Claim 11.35, printed p. 291. -/
theorem blowup_curvatureTensorNorm_le_of_step_cylinders
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {M B c : ℝ} (hc : 0 < c)
    (hstage : ∀ n : ℕ, ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop,
      ∃ e : ControlledBlowupCylinder S k A ((n : ℝ) * c) B 1,
        ∀ s hs x, x ∈ S.baseBall k A →
          (S.flow k).scalar (e.embedding.pointMap s hs x) ≤ M * S.scale k) :
    ∀ t ∈ J, ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection t).curvatureTensorNorm x ≤ M := by
  intro t ht x
  exact ((G.limit.flow.connection t).curvatureTensorNorm_le_scalarCurvature_sharp
    (G.limit.flow.connection t).intrinsicCurvatureTensorCalculus x
    (G.limit.nonnegative_curvature_operator t ht x)).trans
      (blowup_scalar_le_of_step_cylinders G hc hstage t ht x)

end PoincareMT.M32
