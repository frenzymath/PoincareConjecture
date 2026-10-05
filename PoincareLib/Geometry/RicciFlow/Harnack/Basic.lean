import PoincareLib.Geometry.Curvature.Operator.Bounds
import PoincareLib.Geometry.RicciFlow.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Completeness and spacetime energy

These are the unchanged definitions in the frozen M06 snapshot
`contracts/definitions/ricci-flow/DifferentialHarnackAncientFlow.lean`.
The curvature-operator definitions live in `Geometry.Curvature.Operator.Bounds`.
See `references/ricci-flow/mapher/harnack-interface.json` for provenance.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- Completeness for the emetric induced by the specified Riemannian metric. -/
def MetricComplete (g : RiemannianMetric n M) [T3Space M] : Prop :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  CompleteSpace M

/-- Squared speed action for a path in a time-dependent Ricci flow. -/
noncomputable def spacetimeEnergy {J : Set ℝ} (F : RicciFlow n M J)
    (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ s in a..b,
    (F.metric s).inner (γ s)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)

end PoincareMT
