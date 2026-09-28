import PoincareConjecture.Proofs.M10.SmoothMetric
import PoincareConjecture.Definitions.Ch06.ReducedVolume

set_option autoImplicit false

open Bundle ContinuousLinearMap Filter Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T b : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem metric_pairing_continuousOn_backward
    (hwindow : Icc (T - b) T ⊆ J) (q : M) (v w : TangentSpace (𝓡 n) q) :
    ContinuousOn (fun s : ℝ ↦ (F.metric (T - s)).inner q v w) (Icc 0 b) := by
  intro s hs
  have htime : T - s ∈ J := hwindow ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hm := F.smooth.continuousOn (T - s, q) ⟨htime, mem_univ q⟩
  rw [continuousWithinAt_hom_bundle] at hm
  have hc : ContinuousWithinAt
      (fun z : ℝ × M ↦ inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
        (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (fun y ↦ TangentSpace (𝓡 n) y →L[ℝ] ℝ)
        q z.2 q z.2 ((F.metric z.1).inner z.2))
      (J ×ˢ univ) (T - s, q) := hm.2
  have hcoord : ContinuousWithinAt (fun r : ℝ ↦ backwardMetricCoordinates F T q (q, r))
      (Icc 0 b) s := by
    apply hc.comp (x := s)
      ((continuousAt_const.sub continuousAt_id).prodMk continuousAt_const).continuousWithinAt
    intro r hr
    change (T - r, q) ∈ J ×ˢ univ
    exact ⟨hwindow ⟨by linarith [hr.2], by linarith [hr.1]⟩, mem_univ _⟩
  let L := (trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) q).continuousLinearMapAt ℝ q
  have heval := (hcoord.clm_apply (continuousWithinAt_const (b := L v))).clm_apply
    (continuousWithinAt_const (b := L w))
  have heq : (fun r : ℝ ↦ backwardMetricCoordinates F T q (q, r) (L v) (L w)) =
      (fun r ↦ (F.metric (T - r)).inner q v w) := by
    funext r
    exact backwardMetricCoordinates_apply q (q, r) (mem_chart_source _ _) v w
  rwa [heq] at heval

theorem staticEuclideanFlowOn_of_interior_metric_eq
    (hb : 0 < b) (hwindow : Icc (T - b) T ⊆ J)
    (e : Diffeomorph (𝓡 n) (𝓡 n) M (EuclideanSpace ℝ (Fin n)) ∞)
    (heq : ∀ s ∈ Ioo 0 b, ∀ q : M, ∀ v w : TangentSpace (𝓡 n) q,
      (F.metric (T - s)).inner q v w =
        inner ℝ (mfderiv (𝓡 n) (𝓡 n) e q v) (mfderiv (𝓡 n) (𝓡 n) e q w)) :
    IsStaticEuclideanFlowOn F (Icc (T - b) T) := by
  refine ⟨e, ?_⟩
  intro t ht q v w
  have hopen : EqOn (fun s : ℝ ↦ (F.metric (T - s)).inner q v w)
      (fun _ ↦ inner ℝ (mfderiv (𝓡 n) (𝓡 n) e q v) (mfderiv (𝓡 n) (𝓡 n) e q w))
      (Ioo 0 b) := fun s hs ↦ heq s hs q v w
  have hclosed := hopen.of_subset_closure (metric_pairing_continuousOn_backward hwindow q v w)
    continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hb.ne])
  have htime : T - t ∈ Icc 0 b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [sub_sub_cancel] using hclosed htime

end PoincareConjecture.M10
