import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetShift
import PoincareConjecture.Proofs.M14.Sec6_2_SquareVariationConstruction
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p) (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))



noncomputable def gaugeShiftFamily (z : ℝ × ℝ) : G.Point :=
  (G.gaugeCover.cylinder b).toSpacetime ((lift (R.curve z.1)).1,
    (G.gaugeCover.spatial b).affineShift (lift (R.curve z.1)).2 (z.2 • η z.1))



noncomputable def supportedGaugeFamily (z : ℝ × ℝ) : G.Point := by
  classical
  exact if z.1 ∈ tsupport η then gaugeShiftFamily R b lift η z else R.curve z.1



theorem supportedGaugeFamily_eq_of_not_tsupport {z : ℝ × ℝ} (hz : z.1 ∉ tsupport η) :
    supportedGaugeFamily R b lift η z = R.curve z.1 := by
  simp only [supportedGaugeFamily, if_neg hz]



theorem supportedGaugeFamily_eq_gauge {z : ℝ × ℝ}
    (hz : (G.gaugeCover.cylinder b).toSpacetime (lift (R.curve z.1)) = R.curve z.1) :
    supportedGaugeFamily R b lift η z = gaugeShiftFamily R b lift η z := by
  by_cases hs : z.1 ∈ tsupport η
  · simp only [supportedGaugeFamily, if_pos hs]
  · rw [supportedGaugeFamily_eq_of_not_tsupport R b lift η hs]
    simp only [gaugeShiftFamily, image_eq_zero_of_notMem_tsupport hs, smul_zero,
      TopologicalSpace.Opens.affineShift_zero, Prod.mk.eta]
    exact hz.symm



theorem supportedGaugeFamily_at_zero
    (hsrc : ∀ s ∈ tsupport η,
      (G.gaugeCover.cylinder b).toSpacetime (lift (R.curve s)) = R.curve s) (s : ℝ) :
    supportedGaugeFamily R b lift η (s, 0) = R.curve s := by
  by_cases hs : s ∈ tsupport η
  · rw [supportedGaugeFamily_eq_gauge R b lift η (hsrc s hs)]
    simp only [gaugeShiftFamily, zero_smul, TopologicalSpace.Opens.affineShift_zero,
      Prod.mk.eta, hsrc s hs]
  · exact supportedGaugeFamily_eq_of_not_tsupport R b lift η hs



theorem supportedGaugeFamily_time
    (hclock : ∀ s ∈ tsupport η, (lift (R.curve s)).1.val =
      G.spacetime.timeFunction (R.curve s)) {s v : ℝ}
    (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    G.spacetime.timeFunction (supportedGaugeFamily R b lift η (s, v)) = T - s ^ 2 := by
  by_cases hsupport : s ∈ tsupport η
  · simp only [supportedGaugeFamily, if_pos hsupport, gaugeShiftFamily,
      (G.gaugeCover.cylinder b).time_eq, hclock s hsupport, R.curve_time s hs]
  · rw [supportedGaugeFamily_eq_of_not_tsupport R b lift η hsupport, R.curve_time s hs]



theorem gaugeShiftFamily_contMDiffAt {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hη : ContDiff ℝ ∞ η) {z : ℝ × ℝ}
    (hs : z.1 ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (hz : R.curve z.1 ∈ U)
    (hshift : (lift (R.curve z.1)).2.val + z.2 • η z.1 ∈ G.gaugeCover.spatial b) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (gaugeShiftFamily R b lift η) z := by
  have hR : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun w : ℝ × ℝ => R.curve w.1) z :=
    ((R.smooth.mono R.interval_subset _ (Ioo_subset_Icc_self hs)).contMDiffAt
      (Icc_mem_nhds hs.1 hs.2)).comp z contMDiffAt_fst
  have hL := ((hlift _ hz).contMDiffAt (hU.mem_nhds hz)).comp z hR
  have hv : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (fun w : ℝ × ℝ => w.2 • η w.1) z :=
    contMDiffAt_snd.smul (hη.contMDiff.contMDiffAt.comp z contMDiffAt_fst)
  have hS := (((G.gaugeCover.spatial b).affineShift_contMDiffOn _ hshift).contMDiffAt
    ((G.gaugeCover.spatial b).affineShift_domain_isOpen.mem_nhds hshift)).comp z
      (hL.snd.prodMk hv)
  exact (G.gaugeCover.cylinder b).smooth.contMDiffAt.comp z (hL.fst.prodMk hS)



theorem supportedGaugeFamily_contMDiffOn {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hη : ContDiff ℝ ∞ η)
    (hsupport : tsupport η ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (hsrc : ∀ s ∈ tsupport η, R.curve s ∈ U) {P : Set ℝ}
    (hshift : ∀ s ∈ tsupport η, ∀ v ∈ P,
      (lift (R.curve s)).2.val + v • η s ∈ G.gaugeCover.spatial b) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (supportedGaugeFamily R b lift η) (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) := by
  have hbase : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z : ℝ × ℝ => R.curve z.1) (M14SqrtParameterInterval τ₁ τ₂ ×ˢ P) :=
    (R.smooth.mono R.interval_subset).comp contMDiffOn_fst (fun _ hz => hz.1)
  intro z hz
  by_cases hsupportz : z.1 ∈ tsupport η
  · have hs := hsupport hsupportz
    have hR : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
        (fun w : ℝ × ℝ => R.curve w.1) z :=
      ((R.smooth.mono R.interval_subset _ (Ioo_subset_Icc_self hs)).contMDiffAt
        (Icc_mem_nhds hs.1 hs.2)).comp z contMDiffAt_fst
    have heq : supportedGaugeFamily R b lift η =ᶠ[𝓝 z] gaugeShiftFamily R b lift η := by
      filter_upwards [hR.continuousAt.preimage_mem_nhds (hU.mem_nhds (hsrc _ hsupportz))]
        with w hw
      exact supportedGaugeFamily_eq_gauge R b lift η (hright _ hw)
    exact ((gaugeShiftFamily_contMDiffAt R b lift η hU hlift hη hs (hsrc _ hsupportz)
      (hshift _ hsupportz _ hz.2)).congr_of_eventuallyEq heq).contMDiffWithinAt
  · have heq : supportedGaugeFamily R b lift η =ᶠ[𝓝 z] fun w => R.curve w.1 := by
      filter_upwards [((isClosed_tsupport η).isOpen_compl.preimage continuous_fst).mem_nhds
        hsupportz] with w hw
      exact supportedGaugeFamily_eq_of_not_tsupport R b lift η hw
    exact (hbase z hz).congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds

end PoincareConjecture.M14
