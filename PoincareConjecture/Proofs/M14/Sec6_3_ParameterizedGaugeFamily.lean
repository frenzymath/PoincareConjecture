import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetShift
import PoincareConjecture.Definitions.M14GeneralizedLGeometry

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
  (f : ℝ × P → G.Point) (j : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j) (χ : ℝ → ℝ) (d : P → EuclideanSpace ℝ (Fin n))

noncomputable def gaugeTranslateFamily (z : ℝ × P) : G.Point :=
  (G.gaugeCover.cylinder j).toSpacetime ((lift (f z)).1,
    (G.gaugeCover.spatial j).affineShift (lift (f z)).2 (χ z.1 • d z.2))

noncomputable def supportedGaugeTranslateFamily (z : ℝ × P) : G.Point := by
  classical
  exact if z.1 ∈ tsupport χ then gaugeTranslateFamily f j lift χ d z else f z

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in

theorem supportedGaugeTranslateFamily_eq_gauge {z : ℝ × P}
    (hz : (G.gaugeCover.cylinder j).toSpacetime (lift (f z)) = f z) :
    supportedGaugeTranslateFamily f j lift χ d z = gaugeTranslateFamily f j lift χ d z := by
  by_cases hs : z.1 ∈ tsupport χ
  · simp only [supportedGaugeTranslateFamily, if_pos hs]
  · simp only [supportedGaugeTranslateFamily, if_neg hs, gaugeTranslateFamily,
      image_eq_zero_of_notMem_tsupport hs, zero_smul,
      TopologicalSpace.Opens.affineShift_zero, Prod.mk.eta, hz]

theorem supportedGaugeTranslateFamily_contMDiffOn {C : Set ℝ} {U : Set P} {V : Set G.Point}
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P))) (spacetimeModel n) ∞ f (C ×ˢ U))
    (hV : IsOpen V) (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift V)
    (hright : ∀ q ∈ V, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    (hχ : ContDiff ℝ ∞ χ) (hd : ContDiffOn ℝ ∞ d U)
    (hsrc : ∀ z ∈ C ×ˢ U, z.1 ∈ tsupport χ → f z ∈ V)
    (hshift : ∀ z ∈ C ×ˢ U, z.1 ∈ tsupport χ →
      (lift (f z)).2.val + χ z.1 • d z.2 ∈ G.gaugeCover.spatial j) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P))) (spacetimeModel n) ∞
      (supportedGaugeTranslateFamily f j lift χ d) (C ×ˢ U) := by
  intro z hz
  by_cases hs : z.1 ∈ tsupport χ
  · have hzV := hsrc z hz hs
    have hL := ((hlift _ hzV).contMDiffAt (hV.mem_nhds hzV)).comp_contMDiffWithinAt z (hf z hz)
    have hd' : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (fun w : ℝ × P => χ w.1 • d w.2) (C ×ˢ U) z :=
      (hχ.contMDiff.contMDiffAt.comp_contMDiffWithinAt z contMDiffWithinAt_fst).smul
        ((hd.contMDiffOn z.2 hz.2).comp z contMDiffWithinAt_snd (fun _ hw => hw.2))
    have hS := (((G.gaugeCover.spatial j).affineShift_contMDiffOn _ (hshift z hz hs)).contMDiffAt
      ((G.gaugeCover.spatial j).affineShift_domain_isOpen.mem_nhds
        (hshift z hz hs))).comp_contMDiffWithinAt z (hL.snd.prodMk hd')
    have hG := (G.gaugeCover.cylinder j).smooth.contMDiffAt.comp_contMDiffWithinAt z
      (hL.fst.prodMk hS)
    have heq : supportedGaugeTranslateFamily f j lift χ d
        =ᶠ[𝓝[C ×ˢ U] z] gaugeTranslateFamily f j lift χ d := by
      filter_upwards [(hf z hz).continuousWithinAt.preimage_mem_nhdsWithin
        (hV.mem_nhds hzV)] with w hw
      exact supportedGaugeTranslateFamily_eq_gauge f j lift χ d (hright _ hw)
    exact hG.congr_of_eventuallyEq heq
      (supportedGaugeTranslateFamily_eq_gauge f j lift χ d (hright _ hzV))
  · have heq : supportedGaugeTranslateFamily f j lift χ d =ᶠ[𝓝 z] f := by
      filter_upwards [((isClosed_tsupport χ).isOpen_compl.preimage continuous_fst).mem_nhds hs]
        with w hw
      simp only [supportedGaugeTranslateFamily, if_neg hw]
    exact (hf z hz).congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

end PoincareConjecture.M14
