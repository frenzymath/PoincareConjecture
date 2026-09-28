import PoincareConjecture.Proofs.M32.Claim11_35.Continuation.LimitScalarBound
import PoincareConjecture.Proofs.M04.CurvatureCalculus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds











set_option autoImplicit false

open Filter
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space




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
    (G.limit.flow.connection t).curvatureTensorCalculus x
    (G.limit.nonnegative_curvature_operator t ht x)).trans
      (blowup_scalar_le_of_step_cylinders G hc hstage t ht x)

end PoincareConjecture.M32
