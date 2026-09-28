





import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Extraction.CrossRadius
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Limit.ClosedBallTransition








open Set Filter Topology Metric
open scoped Topology

noncomputable section

namespace Poincare.GromovHausdorff







theorem exists_subseq_compatible_marked_closedBall_limits_with_inner_ball_range_of_uniform_packing_bounds
    (X : Nat -> BasedMetricSpaceBundle.{0})
    [forall k, CompleteSpace (X k).carrier]
    (hpack : forall delta radius, 0 < delta -> exists N : Nat, forall k n,
      n ∈ packingAdmissible (X k).base delta radius → n ≤ N) :
    exists phi : Nat -> Nat,
      exists S : CompatiblePointedCompactSystem.{0},
        StrictMono phi /\
          (∀ i, Metric.ball (S.stage (i + 1)).base (i : Real) ⊆
            Set.range (S.transition i)) /\
          forall i, exists R : VaryingRealizationSequence
              (fun n => ((uniformPackingBoundedClosedBall X hpack (phi n) i)
                |>.toFiniteDiameterBasedMetricSpace).toBasedMetricSpaceBundle)
              ((S.stage i).toFiniteDiameterBasedMetricSpace
                |>.toBasedMetricSpaceBundle),
            Tendsto
                (fun n => @Metric.hausdorffDist (R.ambient n).carrier
                  inferInstance (Set.range (R.left n)) (Set.range (R.right n)))
                atTop (nhds 0) /\
              PointedGHConverges
                (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
                  |>.toFiniteDiameterBasedMetricSpace)
                (S.stage i).toFiniteDiameterBasedMetricSpace := by
  obtain ⟨phi, Y, hphi, hmarked⟩ :=
    exists_subseq_marked_closedBall_realizations_of_uniform_packing_bounds
      X hpack
  have hconv : forall i, PointedGHConverges
      (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
        |>.toFiniteDiameterBasedMetricSpace)
      (Y i).toFiniteDiameterBasedMetricSpace := by
    intro i
    exact (Classical.choose_spec (hmarked i)).2
  have hexists (i : Nat) :
      exists e : (Y i).carrier -> (Y (i + 1)).carrier,
        Isometry e /\ e (Y i).base = (Y (i + 1)).base /\
          Metric.ball (Y (i + 1)).base (i : Real) ⊆ Set.range e :=
    exists_basedIsometricEmbedding_between_marked_closedBall_limits_with_inner_ball_range
      X hpack phi Y hconv i
  choose transition transition_isometry transition_base transition_range
    using hexists
  let S : CompatiblePointedCompactSystem.{0} :=
    { stage := Y
      transition := transition
      transition_isometry := transition_isometry
      transition_base := transition_base }
  refine ⟨phi, S, hphi, ?_, ?_⟩
  · intro i
    simpa [S] using transition_range i
  · intro i
    change exists R : VaryingRealizationSequence
        (fun n => ((uniformPackingBoundedClosedBall X hpack (phi n) i)
          |>.toFiniteDiameterBasedMetricSpace).toBasedMetricSpaceBundle)
        ((Y i).toFiniteDiameterBasedMetricSpace.toBasedMetricSpaceBundle),
      Tendsto
          (fun n => @Metric.hausdorffDist (R.ambient n).carrier inferInstance
            (Set.range (R.left n)) (Set.range (R.right n)))
          atTop (nhds 0) /\
        PointedGHConverges
          (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
            |>.toFiniteDiameterBasedMetricSpace)
          (Y i).toFiniteDiameterBasedMetricSpace
    exact hmarked i





theorem exists_subseq_compatible_marked_closedBall_limits_with_proper_completedLimit_of_uniform_packing_bounds
    (X : Nat -> BasedMetricSpaceBundle.{0})
    [forall k, CompleteSpace (X k).carrier]
    (hpack : forall delta radius, 0 < delta -> exists N : Nat, forall k n,
      n ∈ packingAdmissible (X k).base delta radius → n ≤ N) :
    exists phi : Nat -> Nat,
      exists S : CompatiblePointedCompactSystem.{0},
        StrictMono phi /\
          ProperSpace S.completedLimit.carrier /\
          (∀ i, Metric.ball (S.stage (i + 1)).base (i : Real) ⊆
            Set.range (S.transition i)) /\
          forall i, exists R : VaryingRealizationSequence
              (fun n => ((uniformPackingBoundedClosedBall X hpack (phi n) i)
                |>.toFiniteDiameterBasedMetricSpace).toBasedMetricSpaceBundle)
              ((S.stage i).toFiniteDiameterBasedMetricSpace
                |>.toBasedMetricSpaceBundle),
            Tendsto
                (fun n => @Metric.hausdorffDist (R.ambient n).carrier
                  inferInstance (Set.range (R.left n)) (Set.range (R.right n)))
                atTop (nhds 0) /\
              PointedGHConverges
                (fun n => (uniformPackingBoundedClosedBall X hpack (phi n) i)
                  |>.toFiniteDiameterBasedMetricSpace)
                (S.stage i).toFiniteDiameterBasedMetricSpace := by
  obtain ⟨phi, S, hphi, hinner, hreal⟩ :=
    exists_subseq_compatible_marked_closedBall_limits_with_inner_ball_range_of_uniform_packing_bounds
      X hpack
  have hcover :=
    S.radial_stage_coverage_of_inner_ball_range hinner
  letI : ProperSpace S.completedLimit.carrier :=
    S.properSpace_completedLimit_of_radial_stage_coverage hcover
  exact ⟨phi, S, hphi, inferInstance, hinner, hreal⟩

end Poincare.GromovHausdorff

end

