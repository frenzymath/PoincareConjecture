import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallLocalBackwardModels
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallSourcePacket
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenMetricCurvaturePositivity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily






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

end PoincareConjecture.M28.CounterexampleNeckFamily
