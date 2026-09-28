import PoincareConjecture.Proofs.M14.Sec6_5_LaplacianBound
import PoincareConjecture.Proofs.M14.Sec6_5_TimeIdentity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point} (E : M14ExponentialFamily G T x)
  {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
  (H : M14StableSet G T (s ^ 2) x E) (hZ : Z ∈ H.carrier)

include hpos hZ in

theorem stableEndpoint_eq_exponential : H.endpoint_map Z = E.gamma Z s := by
  rw [H.endpoint_map_eq Z hZ, Real.sqrt_sq hpos.le]

noncomputable def regularStablePath : M14BackwardPath G T 0 (s ^ 2) x (H.endpoint_map Z) :=
  { E.path Z s hs hpos with
    endpoint_time := by
      rw [stableEndpoint_eq_exponential E hpos H hZ]
      exact (E.path Z s hs hpos).endpoint_time
    curve_end := (E.path Z s hs hpos).curve_end.trans
      (stableEndpoint_eq_exponential E hpos H hZ).symm }

theorem regularStablePath_minimizing : M14IsMinimizing (regularStablePath E hs hpos H hZ) := by
  have hmin := exponentialPath_minimizing_of_uniqueBranch E hpos hs
    (stableInitialVector_unique_branch E ((H.carrier_exact Z).mp hZ))
  intro p
  let q : M14BackwardPath G T 0 (s ^ 2) x (E.gamma Z s) :=
    { p with
      endpoint_time := (E.path Z s hs hpos).endpoint_time
      curve_end := p.curve_end.trans (stableEndpoint_eq_exponential E hpos H hZ) }
  exact hmin q

theorem regularStablePath_actualK_eq :
    M14GeneralizedKIntegral G (regularStablePath E hs hpos H hZ)
      (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
        ((regularStablePath E hs hpos H hZ).curve t)) =
      M14GeneralizedKIntegral G (E.path Z s hs hpos)
        (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          ((E.path Z s hs hpos).curve t)) := rfl

theorem regular_square_endpoint : (E.square_path Z s hs hpos).curve s = E.gamma Z s := by
  apply exponential_square_curve_eq E Z hs hpos
  simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using
    (show s ∈ Icc 0 s from ⟨hpos.le, le_rfl⟩)

include hZ in

theorem regularStable_slicePoint_eq
    (hq : G.spacetime.timeFunction ((E.square_path Z s hs hpos).curve s) = T - s ^ 2) :
    H.endpoint_slice_map Z = ⟨(E.square_path Z s hs hpos).curve s, hq⟩ := by
  apply Subtype.ext
  exact (H.endpoint_slice_map_val Z hZ).trans
    ((stableEndpoint_eq_exponential E hpos H hZ).trans
      (regular_square_endpoint E hs hpos).symm)

theorem reducedLengthAt_stable_joint_time_identity
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hz : (Z, s) ∈ M14JointDomain G E) :
    M14BackwardTimeDerivative G (M14ReducedLengthAt G T 0 x) (H.endpoint_map Z) =
      horizontalScalarCurvature G.leafwise (H.endpoint_map Z) -
        M14ReducedLengthValue G T 0 (s ^ 2) x (H.endpoint_map Z) / s ^ 2 +
        M14GeneralizedKIntegral G (regularStablePath E hs hpos H hZ)
          (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
            ((regularStablePath E hs hpos H hZ).curve t)) /
          (2 * s ^ 2 * Real.sqrt (s ^ 2)) := by
  rw [regularStablePath_actualK_eq]
  have h := reducedLengthAt_joint_time_identity hCoordinates hM04 hM12 E hs hpos hz
    (regular_square_endpoint E hs hpos)
  simpa only [← stableEndpoint_eq_exponential E hpos H hZ] using h

theorem reducedLengthGradientNormSq_stable_joint_identity
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hz : (Z, s) ∈ M14JointDomain G E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal (H.endpoint_map Z)))
    (hb : ∀ i j, G.spacetime.horizontalMetric.inner (H.endpoint_map Z) (b i) (b j) =
      if i = j then 1 else 0) :
    M14ReducedLengthGradientNormSq (T := T) (τ₁ := 0) G x (H.endpoint_map Z) b =
      M14ReducedLengthValue G T 0 (s ^ 2) x (H.endpoint_map Z) / s ^ 2 -
        M14GeneralizedKIntegral G (regularStablePath E hs hpos H hZ)
          (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
            ((regularStablePath E hs hpos H hZ).curve t)) /
          (s ^ 2 * Real.sqrt (s ^ 2)) -
        horizontalScalarCurvature G.leafwise (H.endpoint_map Z) := by
  have h (q : G.Point) (hq : q = E.gamma Z s)
      (b : Module.Basis (Fin n) ℝ (G.Horizontal q))
      (hb : ∀ i j, G.spacetime.horizontalMetric.inner q (b i) (b j) =
        if i = j then 1 else 0) :
      M14ReducedLengthGradientNormSq (T := T) (τ₁ := 0) G x q b =
        M14ReducedLengthValue G T 0 (s ^ 2) x q / s ^ 2 -
          M14GeneralizedKIntegral G (E.path Z s hs hpos)
            (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
              ((E.path Z s hs hpos).curve t)) / (s ^ 2 * Real.sqrt (s ^ 2)) -
          horizontalScalarCurvature G.leafwise q := by
    subst q
    exact reducedLengthGradientNormSq_joint_identity hCoordinates hM04 hM12 E hs hpos hz
      (regular_square_endpoint E hs hpos) b hb
  exact h (H.endpoint_map Z) (stableEndpoint_eq_exponential E hpos H hZ) b hb

theorem reducedLengthLaplacian_stable_joint_bound
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hz : (Z, s) ∈ M14JointDomain G E) :
    M14ReducedLengthLaplacian (τ₁ := 0) G x (H.endpoint_slice_map Z) ≤
      (n : ℝ) / (2 * s ^ 2) - horizontalScalarCurvature G.leafwise (H.endpoint_map Z) -
        M14GeneralizedKIntegral G (regularStablePath E hs hpos H hZ)
          (fun t => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
            ((regularStablePath E hs hpos H hZ).curve t)) /
          (2 * s ^ 2 * Real.sqrt (s ^ 2)) := by
  rw [regularStablePath_actualK_eq]
  have hp := regular_square_endpoint E hs hpos
  have hq : G.spacetime.timeFunction ((E.square_path Z s hs hpos).curve s) = T - s ^ 2 := by
    rw [hp]
    exact E.clock Z s hs
  have h := reducedLengthLaplacian_joint_bound hCoordinates hM04 hM12 E hs hpos hz hp hq
  rw [← regularStable_slicePoint_eq E hs hpos H hZ hq] at h
  simpa only [hp, ← stableEndpoint_eq_exponential E hpos H hZ] using h

end PoincareConjecture.M14
