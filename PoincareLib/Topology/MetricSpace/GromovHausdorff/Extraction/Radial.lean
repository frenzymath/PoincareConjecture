/-
Adapted from AxelWorkspace, revision f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e.
Source: MorganTianLib/Foundations/MarkedRadialLimit.lean.
Apache-2.0; see references/analysis/axel-workspace/LICENSE.Apache-2.0.txt.
-/

import PoincareLib.Topology.MetricSpace.GromovHausdorff.Extraction.CrossRadius
import PoincareLib.Topology.MetricSpace.GromovHausdorff.Limit.ClosedBallTransition

/-!
# marked radial compact-stage limits

The marked diagonal already supplies pointed compact limits at every integer
radius.  This module retains the strict inner-ball range of the limiting
cross-radius embeddings when assembling those limits into a compatible system.
-/

open Set Filter Topology Metric
open scoped Topology

noncomputable section

namespace Poincare.GromovHausdorff

/-- **Math.** Uniform packing bounds produce one marked subsequence whose
integer-radius compact limits form a compatible system, with each consecutive
transition covering the strict inner ball inherited from the canonical
closed-ball inclusion.  The marked realizations and convergence witnesses are
retained for every radius.
-/
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

/-- **Math.** The marked inner-ball diagonal has a proper completed common
ambient: strict inner-ball range of the transitions supplies radial closed-ball
coverage, and hence properness, through the compatible-system converse.
-/
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

#print axioms
  Poincare.GromovHausdorff.exists_subseq_compatible_marked_closedBall_limits_with_inner_ball_range_of_uniform_packing_bounds
#print axioms
  Poincare.GromovHausdorff.exists_subseq_compatible_marked_closedBall_limits_with_proper_completedLimit_of_uniform_packing_bounds
