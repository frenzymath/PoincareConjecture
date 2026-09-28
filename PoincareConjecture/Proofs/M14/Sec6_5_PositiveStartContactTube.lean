import PoincareConjecture.Proofs.M14.Sec6_1_GaugePerturbation
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point}

theorem exists_sameEndpointPath_through_gaugeShift
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (p : M14BackwardPath G T a b x y)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j) {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hrec : ∀ q ∈ U, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    {l c r : ℝ} (hal : a < l) (hlc : l < c) (hcr : c < r) (hrb : r < b)
    (hsrc : ∀ s ∈ Ioo l r, p.curve s ∈ U) (q : G.Point) (hq : q ∈ U)
    (hclock : G.spacetime.timeFunction q = T - c)
    (hshift : ∀ s ∈ Ioo l r, ∀ v ∈ Icc (0 : ℝ) 1,
      (lift (p.curve s)).2.val +
        v • ((lift q).2.val - (lift (p.curve c)).2.val) ∈ G.gaugeCover.spatial j) :
    ∃ r : M14BackwardPath G T a b x y, r.curve c = q := by
  obtain ⟨χ, hχsupport, _, hχ, hχrange, hχc⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (isOpen_Ioo.mem_nhds ⟨hlc, hcr⟩)
  let d := (lift q).2.val - (lift (p.curve c)).2.val
  let η : ℝ → EuclideanSpace ℝ (Fin n) := fun s => χ s • d
  have hη : ContDiff ℝ ∞ η := hχ.smul contDiff_const
  have hsupport : tsupport η ⊆ Ioo l r :=
    (tsupport_smul_subset_left χ (fun _ => d)).trans hχsupport
  have hshift' (s : ℝ) (hs : s ∈ tsupport η) :
      (lift (p.curve s)).2.val + (1 : ℝ) • η s ∈ G.gaugeCover.spatial j := by
    simpa only [one_smul, η, d] using hshift s (hsupport hs) (χ s) (hχrange ⟨s, rfl⟩)
  let r := pathOfSupportedGaugePerturbation p j lift η hM12 hU hlift hrec
    hal (hlc.trans hcr) hrb hη hsupport (fun s hs => hsrc s (hsupport hs)) 1 hshift'
  have hcU := hsrc c ⟨hlc, hcr⟩
  have htime : (lift (p.curve c)).1 = (lift q).1 := by
    apply Subtype.ext
    have hpclock := p.curve_time c ⟨(hal.trans hlc).le, (hcr.trans hrb).le⟩
    have hleft := ((G.gaugeCover.cylinder j).time_eq (lift (p.curve c))).symm.trans
      ((congrArg G.spacetime.timeFunction (hrec _ hcU)).trans hpclock)
    have hright := ((G.gaugeCover.cylinder j).time_eq (lift q)).symm.trans
      ((congrArg G.spacetime.timeFunction (hrec q hq)).trans hclock)
    exact hleft.trans hright.symm
  have hpoint : (G.gaugeCover.spatial j).affineShift (lift (p.curve c)).2
      ((1 : ℝ) • η c) = (lift q).2 := by
    apply Subtype.ext
    have hmem : (lift (p.curve c)).2.val + (1 : ℝ) • η c ∈ G.gaugeCover.spatial j := by
      simpa only [η, hχc, one_smul, d, add_sub_cancel] using (lift q).2.property
    rw [(G.gaugeCover.spatial j).affineShift_val hmem]
    simp only [η, hχc, one_smul, d, add_sub_cancel]
  refine ⟨r, ?_⟩
  change supportedBackwardGaugeFamily p j lift η 1 c = q
  rw [supportedBackwardGaugeFamily_eq_gauge p j lift η (hrec _ hcU)]
  change (G.gaugeCover.cylinder j).toSpacetime
    ((lift (p.curve c)).1, (G.gaugeCover.spatial j).affineShift
      (lift (p.curve c)).2 ((1 : ℝ) • η c)) = q
  rw [htime, hpoint]
  exact hrec q hq

theorem exists_pastTube_sameEndpointPaths
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (p : M14BackwardPath G T a b x y) :
    ∃ N : Set G.Point, IsOpen N ∧ y ∈ N ∧
      N ⊆ {q | a < T - G.spacetime.timeFunction q} ∧
      ∀ q ∈ N, T - G.spacetime.timeFunction q < b →
        ∃ r : M14BackwardPath G T a b x y,
          r.curve (T - G.spacetime.timeFunction q) = q := by
  obtain ⟨j, U, lift, hU, hyU, hlift, hrec, _⟩ := exists_smooth_gauge_lift G y
  let z := (lift y).2.val
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (G.gaugeCover.spatial j).isOpen
    z (lift y).2.property
  let W := U ∩ (fun q : G.Point => (lift q).2.val) ⁻¹' Metric.ball z (ε / 4)
  have hW : IsOpen W :=
    (continuous_subtype_val.comp_continuousOn hlift.continuousOn.snd).isOpen_inter_preimage
      hU Metric.isOpen_ball
  have hyW : y ∈ W := ⟨hyU, Metric.mem_ball_self (by positivity)⟩
  have hpW : p.curve ⁻¹' W ∈ 𝓝[Icc a b] b :=
    (p.curve_continuous b ⟨p.tau_lt.le, le_rfl⟩).preimage_mem_nhdsWithin
      (hW.mem_nhds (by rw [p.curve_end]; exact hyW))
  rw [nhdsWithin_Icc_eq_nhdsLE p.tau_lt] at hpW
  obtain ⟨c₁, hc₁, hpre⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp hpW
  obtain ⟨c₀, hc₀left, hc₀right⟩ := exists_between (max_lt p.tau_lt hc₁)
  have hac₀ : a < c₀ := (le_max_left a c₁).trans_lt hc₀left
  have hpN (s : ℝ) (hs : s ∈ Icc c₀ b) : p.curve s ∈ W :=
    hpre ⟨(le_max_right a c₁).trans (hc₀left.le.trans hs.1), hs.2⟩
  let N := W ∩ {q : G.Point | c₀ < T - G.spacetime.timeFunction q}
  have ht : Continuous (fun q : G.Point => G.spacetime.timeFunction q) :=
    (show ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (fun q : G.Point => G.spacetime.timeFunction q) from G.spacetime.time_smooth).continuous
  have hN : IsOpen N := hW.inter (isOpen_lt continuous_const
    (continuous_const.sub ht))
  have hyN : y ∈ N := ⟨hyW, by
    change c₀ < T - G.spacetime.timeFunction y
    rw [p.endpoint_time, sub_sub_cancel]
    exact hc₀right⟩
  refine ⟨N, hN, hyN, (fun _ hq => hac₀.trans hq.2), ?_⟩
  intro q hq hqb
  let c := T - G.spacetime.timeFunction q
  have hqc₀ : c₀ < c := hq.2
  obtain ⟨l, hc₀l, hlc⟩ := exists_between hqc₀
  obtain ⟨r, hcr, hrb⟩ := exists_between hqb
  have hcN : p.curve c ∈ W := hpN c ⟨hq.2.le, hqb.le⟩
  have hd : ‖(lift q).2.val - (lift (p.curve c)).2.val‖ < ε / 2 := by
    have hqz : ‖(lift q).2.val - z‖ < ε / 4 := by
      simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm] using hq.1.2
    have hcz : ‖(lift (p.curve c)).2.val - z‖ < ε / 4 := by
      simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm] using hcN.2
    have htri := norm_sub_le ((lift q).2.val - z) ((lift (p.curve c)).2.val - z)
    have heq : ((lift q).2.val - z) - ((lift (p.curve c)).2.val - z) =
        (lift q).2.val - (lift (p.curve c)).2.val := by abel
    rw [heq] at htri
    linarith
  apply exists_sameEndpointPath_through_gaugeShift hM12 p j lift hU hlift hrec
    (hac₀.trans hc₀l) hlc hcr hrb
    (fun s hs => (hpN s ⟨(hc₀l.trans hs.1).le, (hs.2.trans hrb).le⟩).1) q hq.1.1
    (by dsimp only [c]; ring)
  intro s hs v hv
  apply hball
  have hsN := hpN s ⟨(hc₀l.trans hs.1).le, (hs.2.trans hrb).le⟩
  have hsz : ‖(lift (p.curve s)).2.val - z‖ < ε / 4 := by
    simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm] using hsN.2
  have hsmul : ‖v • ((lift q).2.val - (lift (p.curve c)).2.val)‖ ≤
      ‖(lift q).2.val - (lift (p.curve c)).2.val‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hv.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hv.2
  rw [Metric.mem_ball, dist_eq_norm]
  have hsum := norm_add_le ((lift (p.curve s)).2.val - z)
    (v • ((lift q).2.val - (lift (p.curve c)).2.val))
  have heq : (lift (p.curve s)).2.val +
      v • ((lift q).2.val - (lift (p.curve c)).2.val) - z =
      ((lift (p.curve s)).2.val - z) +
        v • ((lift q).2.val - (lift (p.curve c)).2.val) := by abel
  rw [heq]
  linarith

end PoincareConjecture.M14
