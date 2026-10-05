import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.Formulas.RegularTimeDerivative
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Regularity.Formulas.GradientIdentity

/-!
# The actual regular time identity with K

The genuine backward derivative and integrated Harnack boundary give
the time formula for the same actual selected path. Morgan-Tian
Lemma 6.49 and Theorem 6.50, p. 131.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

/-- The exact regular backward-time identity, with the actual K
integral of the selected exponential path, Theorem 6.50, p. 131. -/
theorem reducedLengthAt_joint_time_identity
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s) :
    M14BackwardTimeDerivative G (M14ReducedLengthAt G T 0 x) (E.gamma Z s) =
      horizontalScalarCurvature G.leafwise (E.gamma Z s) -
        M14ReducedLengthValue G T 0 (s ^ 2) x (E.gamma Z s) / s ^ 2 +
        M14GeneralizedKIntegral G (E.path Z s hs hpos)
          (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
            ((E.path Z s hs hpos).curve t)) / (2 * s ^ 2 * Real.sqrt (s ^ 2)) := by
  have hK := exponential_harnackIntegral_eq hM12 E hs hpos
  have hS := congrArg (horizontalScalarCurvature G.leafwise) hpoint
  rw [hS] at hK
  obtain ⟨_, _, _, _, _, hl⟩ := jointDomain_action_branch E hz
  rw [E.reduced_length_eq Z s hs hpos] at hl
  rw [reducedLengthAt_time_derivative_square hCoordinates hM04 hM12 E hs hpos hz hpoint,
    ← hl, Real.sqrt_sq hpos.le, hK]
  field_simp [hpos.ne']
  ring

end PoincareMT.M14
