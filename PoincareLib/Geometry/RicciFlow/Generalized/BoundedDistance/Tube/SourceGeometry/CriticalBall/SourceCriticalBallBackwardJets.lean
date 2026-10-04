import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallBackwardBounds
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.ChartBounds
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Geometry.Parabolic.BackwardMetricComparison
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Geometry.Parabolic.MixedBounds
import PoincareLib.Analysis.Calculus.SmoothCompactness.LocalConvergence

/-!
# Actual mixed-jet bounds on buffered backward charts

The retained spatial convergence supplies terminal ellipticity and every
spatial jet bound. The original-neck curvature estimates propagate these
to genuine mixed within jets through both time endpoints. Morgan--Tian
Proposition 5.14 and Claims 10.10-10.11, pp. 90-91 and 254-255;
M28 derivation 76.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {T : ∀ k, SourceTubeData (H.segment k)}
  {A1 : ℝ} {hA1 : 0 < A1} {phi : ℕ → ℕ}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric T A1 (phi k))
    (fun k => H.tubeCriticalBase T A1 hA1 (phi k))}
  {q : G.limitCarrier.carrier} {a : ℝ}
  (D : CriticalBallBackwardChartData H T A1 hA1 phi G q a)

/-- The closed smaller ball used for uniform derivative estimates, strictly
inside the open source chart (derivation 76). -/
def testSet : Set (EuclideanSpace ℝ (Fin 3)) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  exact closedBall (extChartAt (𝓡 3) q q) D.radius

/-- The tested coordinate set is compact in the fixed Euclidean topology
(Proposition 5.14; derivation 76). -/
theorem testSet_compact : IsCompact D.testSet := isCompact_closedBall _ _

/-- The positive spatial buffer puts every tested point strictly inside
the domain where the totalized source map is geometric (derivation 76). -/
theorem testSet_subset_domain : D.testSet ⊆ D.domain :=
  closedBall_subset_ball (by linarith [D.radius_pos])

set_option synthInstance.maxHeartbeats 200000 in
-- The normed coefficient space uses the dependent original source metric.
set_option maxHeartbeats 1600000 in
-- The coefficient norm retains the dependent original source flow.
/-- The source terminal jets inherit the actual spatial-limit bounds after
the same finite prefix. The threshold still depends on the order (derivation 76). -/
theorem terminal_jet_bounds (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ x ∈ D.testSet,
      ‖iteratedFDeriv ℝ m
        (((D.sourceFlow k).metric 0).pullbackCoefficients (D.parametrization k)) x‖ ≤ B := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  have htarget : D.testSet ⊆ (extChartAt (𝓡 3) q).target :=
    D.testSet_subset_domain.trans (ball_subset_closedBall.trans D.target)
  obtain ⟨B, hB, hbound⟩ := G.exists_eventual_chart_jet_bound q m D.testSet
    D.testSet_compact htarget
  refine ⟨B, zero_le_one.trans hB, ?_⟩
  filter_upwards [(tendsto_add_atTop_nat D.offset).eventually hbound] with k hk
  intro x hx
  rw [eqOn_iteratedFDeriv_of_isOpen D.domain_open (D.terminal_coefficients k) m
    (D.testSet_subset_domain hx)]
  exact hk x hx

set_option maxHeartbeats 1600000 in
-- Coefficient equality unfolds the retained dependent source metric.
/-- The positive limiting spatial metric gives terminal ellipticity for
the actual selected source flows on the tested compact ball (derivation 76). -/
theorem terminal_ellipticity :
    ∃ alpha beta : ℝ, 0 < alpha ∧ 0 < beta ∧ ∀ᶠ k in atTop, ∀ x ∈ D.testSet,
      ∀ v : EuclideanSpace ℝ (Fin 3),
        alpha * ‖v‖ ^ 2 ≤ ((D.sourceFlow k).metric 0).pullbackCoefficients
          (D.parametrization k) x v v ∧
        ((D.sourceFlow k).metric 0).pullbackCoefficients
          (D.parametrization k) x v v ≤ beta * ‖v‖ ^ 2 := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  have htarget : D.testSet ⊆ (extChartAt (𝓡 3) q).target :=
    D.testSet_subset_domain.trans (ball_subset_closedBall.trans D.target)
  obtain ⟨alpha, beta, ha, hb, hbound⟩ := G.exists_eventual_chart_ellipticity
    q D.testSet D.testSet_compact htarget
  refine ⟨alpha, beta, ha, hb, ?_⟩
  filter_upwards [(tendsto_add_atTop_nat D.offset).eventually hbound] with k hk
  intro x hx v
  rw [D.terminal_coefficients k (D.testSet_subset_domain hx)]
  exact hk x hx v

set_option maxHeartbeats 1600000 in
-- The time comparison is applied to the actual dependent source flow.
/-- A global source curvature bound propagates terminal ellipticity to
the common included backward interval on the tested chart (derivation 76). -/
theorem evolving_ellipticity {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ k t, t ∈ Icc (-(a / 8)) 0 → ∀ x : strongNeckOpen (D.neck k),
      ((D.sourceFlow k).connection t).curvatureTensorNorm x ≤ K) :
    ∃ alpha beta : ℝ, 0 < alpha ∧ 0 ≤ beta ∧ ∀ᶠ k in atTop,
      ∀ t ∈ Icc (-(a / 8)) 0, ∀ x ∈ D.testSet, ∀ v : EuclideanSpace ℝ (Fin 3),
        alpha * ‖v‖ ^ 2 ≤ ((D.sourceFlow k).metric t).pullbackCoefficients
          (D.parametrization k) x v v ∧
        ((D.sourceFlow k).metric t).pullbackCoefficients
          (D.parametrization k) x v v ≤ beta * ‖v‖ ^ 2 := by
  obtain ⟨alpha, beta, ha, hb, hterminal⟩ := D.terminal_ellipticity
  refine ⟨Real.exp (-2 * (3 : ℝ) * K * (a / 8)) * alpha,
    Real.exp (2 * (3 : ℝ) * K * (a / 8)) * beta,
    mul_pos (Real.exp_pos _) ha, (mul_pos (Real.exp_pos _) hb).le, ?_⟩
  filter_upwards [hterminal] with k hk
  intro t ht x hx v
  exact backward_pullback_ellipticity (D.sourceFlow k) (by linarith [D.scale_pos]) hK
    (D.parametrization k) x (fun s hs => hcurv k s hs _) (hk x hx) ht v

set_option synthInstance.maxHeartbeats 200000 in
-- Typeclass synthesis follows the actual source flow through its captured chart.
set_option maxHeartbeats 1600000 in
-- The actual full-neck flows and canonical parametrizations remain dependent on k.
/-- The original flow bounds and retained spatial metric produce all mixed
within jets on the buffered chart, including both time endpoints.
The supplied curvature bounds are constructed in BackwardBounds (derivation 76). -/
theorem mixed_jet_bounds {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ k t, t ∈ Icc (-(a / 8)) 0 → ∀ x : strongNeckOpen (D.neck k),
      ((D.sourceFlow k).connection t).curvatureTensorNorm x ≤ K)
    (hderiv : ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ k t, t ∈ Icc (-(a / 8)) 0 →
      ∀ x ∈ D.domain, ((D.sourceFlow k).connection t).curvatureDerivativeNorm m
        (D.parametrization k x) ≤ B) :
    ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      ∀ z ∈ Icc (-(a / 8)) 0 ×ˢ D.testSet,
        ‖iteratedFDerivWithin ℝ m
          (fun z => ((D.sourceFlow k).metric z.1).pullbackCoefficients
            (D.parametrization k) z.2) (Icc (-(a / 8)) 0 ×ˢ D.domain) z‖ ≤ B := by
  obtain ⟨alpha, beta, ha, hb, hell⟩ := D.evolving_ellipticity hK hcurv
  apply eventually_within_bounds_closed_backward_of_curvature atTop
    (by linarith [D.scale_pos] : 0 < a / 8) D.sourceFlow
    (fun _ => D.domain) (fun _ => D.testSet) D.parametrization
    (fun _ => D.domain_open) (fun _ => D.testSet_subset_domain)
    D.parametrization_smooth (fun k _ hx => D.parametrization_invertible k hx)
    ha hb hell
  · intro m
    obtain ⟨B, hB, hbound⟩ := hderiv m
    exact ⟨B, hB.le, Eventually.of_forall (fun k t ht x hx =>
      hbound k t (Ioo_subset_Icc_self ht) x (D.testSet_subset_domain hx))⟩
  · exact D.terminal_jet_bounds

end PoincareMT.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData
