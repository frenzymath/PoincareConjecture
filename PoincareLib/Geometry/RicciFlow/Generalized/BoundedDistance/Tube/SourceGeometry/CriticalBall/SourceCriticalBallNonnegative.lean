import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallLocalBackwardModels
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.CriticalBall.CriticalBallSourcePacket
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.OpenGeometry.OpenMetricCurvaturePositivity

/-!
# Actual curvature positivity on the retained first spatial limit

At each point the original counterexample sources produce an included
terminal slice of a nonnegative backward model. Its actual local isometry
transports positivity to the same retained connection D0. Open restriction
then gives the sectional curvature input for the selected-end comparison.
Source: Morgan--Tian Claim 10.11, p. 255; M28 derivations 79 and 161b.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M28.CounterexampleNeckFamily

/-- The actual original sources give nonnegative curvature operator on
the same first spatial limit, and nonnegative sectional curvature for
every literal open restriction. The accuracy is chosen before the
counterexample family and source packet; the local models are produced
internally. Source: MT Claim 10.11, p. 255; derivation 161b. -/
theorem exists_source_criticalBall_nonnegative_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ D0 : LeviCivitaData G.limitMetric,
            (∀ q : G.limitCarrier.carrier, D0.NonnegativeCurvatureOperator q) ∧
            ∀ (U : TopologicalSpace.Opens G.limitCarrier.carrier)
              (DU : LeviCivitaData (intrinsicOpenMetric G.limitMetric U)),
              DU.NonnegativeSectionalCurvature := by
  obtain ⟨epsilon0, hpos, hsmall, hmodels⟩ :=
    exists_source_criticalBall_local_backward_models_accuracy P
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D0
  have hnonnegative (q : G.limitCarrier.carrier) :
      D0.NonnegativeCurvatureOperator q := by
    obtain ⟨F⟩ := hmodels H W.tube hepsilon W.radius W.radius_pos W.high_index
      W.high_index_strictMono G D0 q univ isOpen_univ (mem_univ q)
    let := F.carrier.topologicalSpace
    let := F.carrier.chartedSpace
    let := F.carrier.isManifold
    obtain ⟨z, hz⟩ := F.captures
    have hzero : (0 : ℝ) ∈ Icc (-F.duration) 0 :=
      ⟨neg_nonpos.mpr F.duration_pos.le, le_rfl⟩
    have htransport := ((F.flow.connection 0).nonnegativeCurvatureOperator_iff_of_local_isometry
      D0 (f := F.embedding) isOpen_univ F.embedding_smooth.contMDiff.contMDiffOn
      (fun y _ v w => (F.metric_at_zero y v w).symm) (mem_univ z)).mp
        (F.nonnegative 0 hzero z)
    rw [hz] at htransport
    exact htransport
  refine ⟨hnonnegative, ?_⟩
  intro U DU
  exact intrinsicOpenMetric_nonnegativeSectionalCurvature_of_operator
    G.limitMetric U D0 DU (fun x => hnonnegative (x : G.limitCarrier.carrier))

end PoincareMT.M28.CounterexampleNeckFamily
