import PoincareConjecture.Proofs.M14.Sec6_5_GradientNorm
import PoincareConjecture.Proofs.M14.Sec6_5_HarnackIntegral

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem exponential_harnackIntegral_eq
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) :
    M14GeneralizedKIntegral G (E.path Z s hs hpos)
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          ((E.path Z s hs hpos).curve t)) =
      E.action Z s / 2 -
        (s ^ 3 * horizontalScalarCurvature G.leafwise ((E.square_path Z s hs hpos).curve s) +
          s * G.spacetime.horizontalMetric.inner ((E.square_path Z s hs hpos).curve s)
            ((E.square_path Z s hs hpos).horizontal_velocity s)
            ((E.square_path Z s hs hpos).horizontal_velocity s) / 4) := by
  have h := squareRoot_harnackIntegral_zero_start hM12 (E.square_path Z s hs hpos)
    (E.square_extension Z s hs hpos) (by
      intro r hr
      apply E.square_euler Z s hs hpos r
      simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using Ioo_subset_Icc_self hr)
  rw [Real.sqrt_sq hpos.le, ← E.action_eq Z s hs hpos] at h
  exact h

theorem reducedLengthGradientNormSq_joint_identity
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hz : (Z, s) ∈ M14JointDomain G E)
    (hpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal (E.gamma Z s)))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner (E.gamma Z s) (b i) (b j) =
      if i = j then 1 else 0) :
    M14ReducedLengthGradientNormSq (T := T) (τ₁ := 0) G x (E.gamma Z s) b =
      M14ReducedLengthValue G T 0 (s ^ 2) x (E.gamma Z s) / s ^ 2 -
        M14GeneralizedKIntegral G (E.path Z s hs hpos)
          (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
            ((E.path Z s hs hpos).curve t)) / (s ^ 2 * Real.sqrt (s ^ 2)) -
        horizontalScalarCurvature G.leafwise (E.gamma Z s) := by
  have hK := exponential_harnackIntegral_eq hM12 E hs hpos
  have hS := congrArg (horizontalScalarCurvature G.leafwise) hpoint
  rw [hS] at hK
  obtain ⟨_, _, _, _, _, hl⟩ := jointDomain_action_branch E hz
  rw [E.reduced_length_eq Z s hs hpos] at hl
  rw [reducedLengthGradientNormSq_eq_squareEnergy hCoordinates hM04 hM12 E hs hpos hz hpoint b hb,
    ← hl, Real.sqrt_sq hpos.le, hK]
  field_simp [hpos.ne']
  ring

end PoincareConjecture.M14
