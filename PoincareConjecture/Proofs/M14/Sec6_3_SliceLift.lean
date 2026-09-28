import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SliceMap












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {t : ℝ} {f : M → (G.slices t).Point} {S : Set M} {z : M}





theorem contMDiffWithinAt_slice_of_inclusion
    (hf : ContMDiffWithinAt J (spacetimeModel n) ∞ (fun a => (f a).val) S z) :
    ContMDiffWithinAt J (𝓡 n) ∞ f S z := by
  obtain ⟨b, U, lift, hU, hzU, hlift, hrec, htime⟩ := exists_smooth_gauge_lift G (f z).val
  have ht : t ∈ (G.gaugeCover.interval b).domain := by
    have h := (lift (f z).val).1.property
    rwa [(htime _ hzU).trans (f z).property] at h
  let t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point := ⟨t, ht⟩
  let g := movingGaugeSliceMap (G.gaugeCover.cylinder b).toMovingSpacetimeGauge G.slices t₀
  have hg : ContMDiff (𝓡 n) (𝓡 n) ∞ g :=
    (movingGaugeSliceMap_localDiffeomorph (G.gaugeCover.cylinder b).toMovingSpacetimeGauge
      G.slices (G.gaugeCover.metric b).toMovingSpacetimeGaugeGeometry t₀).contMDiff
  have heq (a : M) (ha : (f a).val ∈ U) : g (lift (f a).val).2 = f a := by
    apply Subtype.ext
    change (G.gaugeCover.cylinder b).toSpacetime (t₀, (lift (f a).val).2) = (f a).val
    have hclock : t₀ = (lift (f a).val).1 :=
      Subtype.ext ((htime _ ha).trans (f a).property).symm
    rw [hclock]
    exact hrec _ ha
  have hc := ((hlift _ hzU).contMDiffAt (hU.mem_nhds hzU)).comp_contMDiffWithinAt z hf
  have hcomp := hg.contMDiffAt.comp_contMDiffWithinAt z hc.snd
  apply hcomp.congr_of_eventuallyEq _ (heq z hzU).symm
  filter_upwards [hf.continuousWithinAt (hU.mem_nhds hzU)] with a ha
  exact (heq a ha).symm




theorem contMDiffAt_slice_of_inclusion
    (hf : ContMDiffAt J (spacetimeModel n) ∞ (fun a => (f a).val) z) :
    ContMDiffAt J (𝓡 n) ∞ f z :=
  (contMDiffWithinAt_slice_of_inclusion (S := univ) hf.contMDiffWithinAt).contMDiffAt univ_mem

end PoincareConjecture.M14
