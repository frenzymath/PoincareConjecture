import PoincareConjecture.Proofs.M14.Sec6_3_GaugeFamilyRestart
import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerRestart
import PoincareConjecture.Proofs.M14.Sec6_3_TimeDomain
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import PoincareConjecture.Proofs.M14.Mathlib.ClosedPrefixPropagation










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in





theorem initialValueCurve_smooth_prefix_from_initial_tube
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T : ℝ} {x : G.Point} (hbase : G.spacetime.timeFunction x = T)
    (ζ : E → G.Horizontal x) (z₀ : E) {S : ℝ} (hS : 0 < S)
    (hsurv : (ζ z₀, S) ∈ initialValueDomain G T x)
    (hstart : ∃ r : ℝ, 0 < r ∧ ∃ U : Set E, IsOpen U ∧ z₀ ∈ U ∧
      (∀ z ∈ U, (ζ z, r) ∈ initialValueDomain G T x) ∧
      ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
        (fun z => initialValueCurve G T x (ζ z.1) z.2) (U ×ˢ Icc 0 r)) :
    ∃ U : Set E, IsOpen U ∧ z₀ ∈ U ∧
      (∀ z ∈ U, (ζ z, S) ∈ initialValueDomain G T x) ∧
      ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
        (fun z => initialValueCurve G T x (ζ z.1) z.2) (U ×ˢ Icc 0 S) := by
  let good : ℝ → Prop := fun s => ∃ U : Set E, IsOpen U ∧ z₀ ∈ U ∧
    (∀ z ∈ U, (ζ z, s) ∈ initialValueDomain G T x) ∧
    ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z => initialValueCurve G T x (ζ z.1) z.2) (U ×ˢ Icc 0 s)
  have hmono {r s : ℝ} (hr : good r) (hs : s ∈ Icc 0 r) : good s := by
    obtain ⟨U, hU, hzU, hsurvU, hγU⟩ := hr
    exact ⟨U, hU, hzU, fun z hz => initialValueDomain_prefix (hsurvU z hz) hs.1 hs.2,
      hγU.mono (prod_mono (Subset.refl _) (Icc_subset_Icc le_rfl hs.2))⟩
  have hinit : ∃ r ∈ Ioc 0 S, good r := by
    obtain ⟨r, hr, hgood⟩ := hstart
    exact ⟨min r S, ⟨lt_min hr hS, min_le_right _ _⟩,
      hmono hgood ⟨(lt_min hr hS).le, min_le_left _ _⟩⟩
  apply closedPrefix_propagation good hmono hinit
  intro t ht
  let γ := initialValueCurve G T x (ζ z₀)
  have hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ γ (Icc 0 S) :=
    (initialValueCurve_time_contMDiffOn hM04 hM12 hbase (ζ z₀)).mono
      (fun _ hs => initialValueDomain_prefix hsurv hs.1 hs.2)
  obtain ⟨b, N, lift, hN, htN, hlift, hrec, hclock⟩ := exists_smooth_gauge_lift G (γ t)
  have hpre : γ ⁻¹' N ∈ 𝓝[Icc 0 S] t :=
    (hγ.continuousOn t ⟨ht.1.le, ht.2⟩).preimage_mem_nhdsWithin (hN.mem_nhds htN)
  obtain ⟨a, c, ha, hat, htc, hcS, hmap, hwindow⟩ :=
    exists_closed_left_neighborhood ht.1 ht.2 hpre
  let β := lift ∘ γ
  have hsub : Icc a c ⊆ Icc 0 S := Icc_subset_Icc ha.le hcS
  have hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc a c) :=
    hlift.comp (hγ.mono hsub) hmap
  have hβclock (s : ℝ) (hs : s ∈ Icc a c) : (β s).1.val = T - s ^ 2 :=
    (hclock (γ s) (hmap hs)).trans (initialValueCurve_clock hbase
      (initialValueDomain_prefix hsurv (hsub hs).1 (hsub hs).2))
  have htime (s : ℝ) (hs : s ∈ Icc a c) :
      T - s ^ 2 ∈ (G.gaugeCover.interval b).domain := hβclock s hs ▸ (β s).1.property
  let t₀ := (β t).1
  let x₀ := (β t).2
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  obtain ⟨y, ⟨P⟩⟩ := (initialValueDomain_positive_iff hS).mp hsurv
  have hC : M14SqrtParameterInterval 0 (S ^ 2) = Icc 0 S := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hS.le]
  have hsubP : Icc a c ⊆ M14SqrtParameterInterval 0 (S ^ 2) := hC ▸ hsub
  have hrecP (s : ℝ) (hs : s ∈ Icc a c) :
      (G.gaugeCover.cylinder b).toSpacetime (β s) = P.square_path.curve s :=
    (hrec (γ s) (hmap hs)).trans (initialValueCurve_eqOn_square hM04 hM12 P (hsubP hs))
  let q := fun s => (β s).2.val
  let ψ := fun s => (q s, M08.chartMomentumVector
    (M08.chartActionMetric W.flow T x₀ (s, q s)) (derivWithin q (Icc a c) s))
  have hac : a < c := hat.trans_le htc
  have hphase : ∀ s ∈ Icc a c, HasDerivWithinAt ψ
      (M08.closedChartEulerPhase W.flow T x₀ (Icc a c) s (ψ s)) (Icc a c) s :=
    squareRootEuler_gauge_phase P.square_path b hCoordinates hscalar W hM04 x₀ hac hsubP
      hβ hrecP hβclock P.extension (fun s hs => P.euler s (hsubP hs))
  have hsrc : (ψ t).1 ∈ (extChartAt (𝓡 n) x₀).target := by
    have heq : extChartAt (𝓡 n) x₀ x₀ = x₀.val := by rw [extChartAt_coe]; rfl
    change x₀.val ∈ (extChartAt (𝓡 n) x₀).target
    rw [← heq]
    exact mem_extChartAt_target x₀
  obtain ⟨l, d, t₁, hld, hal, hdc, hi, hnear, hrest⟩ :=
    exists_closedChartEulerPhase_restart_along W.flow hM04 T x₀ hac htime
      ⟨t, hat.le, htc⟩ ψ hphase hsrc
  have htd : t ≤ d := calc
    t = t₁.val := hi.symm
    _ ≤ d := t₁.property.2
  have hlt : l < t := left_lt_of_Icc_mem_nhdsWithin hat htc hnear
  have h0l : 0 < l := ha.trans_le hal
  have hnearS : Icc l d ∈ 𝓝[Icc 0 S] t := nhdsWithin_le_of_mem hwindow hnear
  obtain ⟨a', c', hla', ha't, htc', _, hrestart, _⟩ :=
    exists_closed_left_neighborhood hlt htd hrest
  refine ⟨a', d, (h0l.trans hla').le, ha't, htd, hdc.trans hcS,
    fun hts => right_lt_of_Icc_mem_nhdsWithin ht.1.le hts hnearS, ?_⟩
  intro r hr hgood
  obtain ⟨U, hU, hzU, hsurvU, hγU⟩ := hgood
  obtain ⟨A, hA, hψA, Ψ, hΨ, hdata⟩ := hrestart ⟨hr.1.le, hr.2.le.trans htc'⟩
  have hlr : l < r := hla'.trans hr.1
  have hrd : r < d := hr.2.trans_le htd
  have hsub' : Icc l d ⊆ Icc a c := Icc_subset_Icc hal hdc
  have hq := gaugeLift_spatialCurve_contDiffOn b hβ
  have hdq := derivWithin_subset hsub' (uniqueDiffOn_Icc hld r ⟨hlr.le, hrd.le⟩)
    ((hq r (hsub' ⟨hlr.le, hrd.le⟩)).differentiableWithinAt (by simp))
  have hcenter : (q r, M08.chartMomentumVector
      (M08.chartActionMetric W.flow T x₀ (r, q r)) (derivWithin q (Icc l d) r)) ∈ A := by
    rw [hdq]
    exact hψA
  obtain ⟨V, hV, hzV, _, hsurvV, hγV⟩ := initialValueCurve_smooth_tube_of_gauge_restart
    hM04 hM12 b W t₀ x₀ h0l.le hlr hrd ζ hU hzU hγU hsurvU hN
    (hmap (hsub' ⟨hlr.le, hrd.le⟩)) lift hlift hrec (hβ.mono hsub')
    (fun s hs => htime s (hsub' hs)) hA hcenter Ψ hΨ hdata
  exact ⟨V, hV, hzV, fun z hz => hsurvV (z, d) ⟨hz, h0l.le.trans hld.le, le_rfl⟩, hγV⟩

end PoincareConjecture.M14
