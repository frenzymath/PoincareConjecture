import PoincareLib.Geometry.Spacetime.GeometryTheory
import PoincareLib.Geometry.Spacetime.Realization.Conclusion
import PoincareLib.Geometry.Spacetime.Realization.Interval.Neighborhood

/-!
# Locality in the retained realization's interval system

Only relatively open interval inclusions are inverted. All maps use the
already selected charts, including at endpoints retained by both intervals.
The local inverse is M11's checked construction output.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

open PoincareMT

namespace Poincare.Spacetime.Realization

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : AdaptedMetricAtlas n X}
  (R : GeneralizedFlowCarrierConclusionWithInterval A)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {IM : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {H' : Type*} [TopologicalSpace H'] {IN : ModelWithCorners ℝ V H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

theorem selectedInterval_smoothAt_of_local (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain) (ho : IsOpen {t : K.domain | t.val ∈ L.domain})
    (t : (R.timeIntervals.interval L).Point) (f : (R.timeIntervals.interval K).Point → N)
    (hf : ContMDiffAt (𝓡∂ 1) IN ∞
      (f ∘ spacetimeIntervalInclusion (R.timeIntervals.interval L)
        (R.timeIntervals.interval K) h) t) :
    ContMDiffAt (𝓡∂ 1) IN ∞ f
      (spacetimeIntervalInclusion (R.timeIntervals.interval L)
        (R.timeIntervals.interval K) h t) := by
  let j := spacetimeIntervalInclusion (R.timeIntervals.interval L) (R.timeIntervals.interval K) h
  have hj := R.interval_localDiffeomorph K L h ho t
  have hi : hj.localInverse (j t) = t := hj.localInverse_left_inv hj.localInverse_mem_target
  have hf' : ContMDiffAt (𝓡∂ 1) IN ∞ (f ∘ j) (hj.localInverse (j t)) := by
    rw [hi]
    exact hf
  apply (hf'.comp (j t) hj.localInverse_contMDiffAt).congr_of_eventuallyEq
  filter_upwards [hj.localInverse_eventuallyEq_right] with s hs
  exact congrArg f hs.symm

theorem selectedInterval_product_smoothAt_of_local (K L : SpacetimeInterval)
    (h : L.domain ⊆ K.domain) (ho : IsOpen {t : K.domain | t.val ∈ L.domain})
    (p : (R.timeIntervals.interval L).Point × M)
    (f : (R.timeIntervals.interval K).Point × M → N)
    (hf : ContMDiffAt ((𝓡∂ 1).prod IM) IN ∞
      (f ∘ Prod.map (spacetimeIntervalInclusion (R.timeIntervals.interval L)
        (R.timeIntervals.interval K) h) id) p) :
    ContMDiffAt ((𝓡∂ 1).prod IM) IN ∞ f
      (spacetimeIntervalInclusion (R.timeIntervals.interval L)
        (R.timeIntervals.interval K) h p.1, p.2) := by
  let j := spacetimeIntervalInclusion (R.timeIntervals.interval L) (R.timeIntervals.interval K) h
  have hj := R.interval_localDiffeomorph K L h ho p.1
  have hi : hj.localInverse (j p.1) = p.1 :=
    hj.localInverse_left_inv hj.localInverse_mem_target
  have hf' : ContMDiffAt ((𝓡∂ 1).prod IM) IN ∞ (f ∘ Prod.map j id)
      (hj.localInverse (j p.1), p.2) := by
    rw [hi]
    exact hf
  have hinv : ContMDiffAt ((𝓡∂ 1).prod IM) ((𝓡∂ 1).prod IM) ∞
      (fun q : (R.timeIntervals.interval K).Point × M => (hj.localInverse q.1, q.2))
      (j p.1, p.2) :=
    (hj.localInverse_contMDiffAt.comp (j p.1, p.2) contMDiffAt_fst).prodMk contMDiffAt_snd
  apply (hf'.comp (j p.1, p.2) hinv).congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt hj.localInverse_eventuallyEq_right] with q hq
  exact congrArg (fun s => f (s, q.2)) hq.symm

/-- A nontrivial interval has arbitrarily small relatively open interval
neighborhoods, also at an included endpoint. -/
theorem interval_exists_open_small_neighborhood (I : SpacetimeInterval) (t : I.domain)
    {U : Set I.domain} (hU : U ∈ 𝓝 t) :
    ∃ J : SpacetimeInterval, ∃ h : J.domain ⊆ I.domain,
      t.val ∈ J.domain ∧ IsOpen {s : I.domain | s.val ∈ J.domain} ∧
        ∀ s : J.domain, (⟨s.val, h s.property⟩ : I.domain) ∈ U := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  let S : Set ℝ := I.domain ∩ Metric.ball t.val r
  have htS : t.val ∈ S := ⟨t.property, Metric.mem_ball_self hr⟩
  have hacc : AccPt t.val (𝓟 S) :=
    ((interval_uniqueDiffOn I t.val t.property).inter (Metric.ball_mem_nhds _ hr)).accPt
  obtain ⟨s, hs, hst⟩ := accPt_iff_nhds.mp hacc univ univ_mem
  let J : SpacetimeInterval := {
    domain := S
    ordConnected := ((interval_convex I).inter (convex_ball _ _)).ordConnected
    nontrivial := ⟨s, hs.2, t.val, htS, hst⟩
  }
  refine ⟨J, inter_subset_left, htS, ?_, fun s => hrU s.property.2⟩
  have he : {s : I.domain | s.val ∈ J.domain} = Metric.ball t r := by
    ext s
    change (s.val ∈ I.domain ∧ dist s.val t.val < r) ↔ dist s t < r
    simp only [s.property, true_and, Subtype.dist_eq]
  rw [he]
  exact Metric.isOpen_ball

end Poincare.Spacetime.Realization
