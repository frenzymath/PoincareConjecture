import PoincareConjecture.Proofs.M47.BlowupControlsCapOutwardTopology
import PoincareConjecture.Proofs.M47.CanonicalCoreBallContainment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem cap_outward_path_length_lower {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hmargin : b + 8 < N.epsilon⁻¹)
    {gamma : ℝ → M} {s t : ℝ} (hst : s ≤ t)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc s t))
    (hmem : MapsTo gamma (Icc s t) N.carrier)
    (hstart : gamma s ∈ N.recutCarrier b)
    (hfinish : gamma t ∈ frontier (N.recutCarrier (b + 8))) :
    ENNReal.ofReal (7 * N.end_neck.scale / 2) ≤ g.pathELength gamma s t := by
  have hcont : ContinuousOn (N.collarHeight b ∘ gamma) (Icc s t) :=
    (N.collarHeight_continuousOn hb (by linarith)).comp hgamma.continuousOn hmem
  have hstartH : N.collarHeight b (gamma s) = b :=
    N.collarHeight_eq_of_mem_recut hstart
  have hfinishH : N.collarHeight b (gamma t) = b + 8 :=
    N.collarHeight_eq_of_mem_frontier (by linarith) hmargin (by linarith) hfinish
  obtain ⟨a, ha, halevel, hafter⟩ := hcont.exists_last_eq_of_lt hst
    (by simpa only [Function.comp_apply, hstartH] using (show b ≤ b + 1 by linarith))
    (by simpa only [Function.comp_apply, hfinishH] using (show b + 1 < b + 8 by linarith))
  change N.collarHeight b (gamma a) = b + 1 at halevel
  have htail : MapsTo gamma (Icc a t) N.end_neck.carrier := by
    intro v hv
    have hcut : b < N.collarHeight b (gamma v) := by
      rcases hv.1.eq_or_lt with heq | hlt
      · subst v
        rw [halevel]
        linarith
      · exact (show b < b + 1 by linarith).trans (hafter v ⟨hlt, hv.2⟩)
    exact (N.collarHeight_above_cutoff hcut).1
  have haH : (N.end_neck.coordinate_inverse (gamma a)).2 = b + 1 := by
    have hcut : b < N.collarHeight b (gamma a) := by rw [halevel]; linarith
    exact (N.collarHeight_above_cutoff hcut).2.symm.trans halevel
  have htH : (N.end_neck.coordinate_inverse (gamma t)).2 = b + 8 := by
    have hcut : b < N.collarHeight b (gamma t) := by rw [hfinishH]; linarith
    exact (N.collarHeight_above_cutoff hcut).2.symm.trans hfinishH
  have hA : 0 < 2 / N.end_neck.scale := div_pos (by norm_num) N.end_neck.scale_pos
  have hbarrier := N.end_neck.height_displacement_le_pathELength_of_axial_speed hA.le
    (fun _ hx v => N.end_neck.coordinate_inverse_axial_le_tangentNorm hx v) ha.2.le
    (hgamma.mono (Icc_subset_Icc_left ha.1)) htail
  rw [htH, haH, show b + 8 - (b + 1) = 7 by ring] at hbarrier
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 7)] at hbarrier
  have hlength : ENNReal.ofReal (7 * N.end_neck.scale / 2) ≤
      g.pathELength gamma a t := by
    apply (ENNReal.mul_le_mul_iff_right
      (ENNReal.ofReal_pos.mpr hA).ne' ENNReal.ofReal_ne_top).mp
    apply le_trans _ hbarrier
    rw [← ENNReal.ofReal_mul hA.le,
      show (2 / N.end_neck.scale) * (7 * N.end_neck.scale / 2) = 7 by
        field_simp [N.end_neck.scale_pos.ne']]
  exact hlength.trans (M36.metric_pathELength_mono g gamma ha.1 le_rfl)

theorem cap_outward_small_ball_subset_recut {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hmargin : b + 8 < N.epsilon⁻¹)
    {y : M} (hy : y ∈ N.recutCarrier b) {r : ℝ} (hr : 0 < r)
    (hrscale : r ≤ 2 * N.end_neck.scale) :
    g.ball y r ⊆ N.recutCarrier (b + 8) := by
  have hb8 : -N.epsilon⁻¹ < b + 8 := by linarith
  have hcapture := N.recutCarrier_compact_closure hb8 hmargin
  have hy8 : y ∈ N.recutCarrier (b + 8) := by
    rcases hy with hcore | hend
    · exact Or.inl hcore
    · exact Or.inr ⟨hend.1, hend.2.1, by linarith [hend.2.2]⟩
  intro z hz
  by_contra hzout
  obtain ⟨gamma, hgamma0, hgamma1, hgamma, hlength, _⟩ :=
    g.exists_short_path_in_ball y z hz
  obtain ⟨t, ht, hfrontier, _, hbefore⟩ := hgamma.continuousOn.exists_first_frontier_time
    zero_le_one (N.recutCarrier_isOpen hb8 hmargin)
    (hgamma0.symm ▸ hy8) (hgamma1.symm ▸ hzout)
  have hbarrier := cap_outward_path_length_lower N hb hmargin ht.1.le
    (hgamma.mono (Icc_subset_Icc_right ht.2))
    (fun s hs => hcapture.2 (hbefore hs)) (hgamma0.symm ▸ hy) hfrontier
  have htotal := hbarrier.trans (M36.metric_pathELength_mono g gamma le_rfl ht.2)
  have hradius : ENNReal.ofReal r ≤ ENNReal.ofReal (7 * N.end_neck.scale / 2) :=
    ENNReal.ofReal_le_ofReal (by linarith [N.end_neck.scale_pos])
  exact not_lt_of_ge (hradius.trans htotal) hlength

theorem cap_outward_small_ball_captured {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hmargin : b + 8 < N.epsilon⁻¹)
    {y : M} (hy : y ∈ N.recutCarrier b) {r : ℝ} (hr : 0 < r)
    (hrscale : r ≤ 2 * N.end_neck.scale) :
    IsCompact (closure (g.ball y r)) ∧ closure (g.ball y r) ⊆ N.carrier := by
  have hcapture := N.recutCarrier_compact_closure (b := b + 8) (by linarith) hmargin
  have hball := closure_mono (cap_outward_small_ball_subset_recut N hb hmargin hy hr hrscale)
  exact ⟨hcapture.1.of_isClosed_subset isClosed_closure hball, hball.trans hcapture.2⟩

end PoincareConjecture.M47
