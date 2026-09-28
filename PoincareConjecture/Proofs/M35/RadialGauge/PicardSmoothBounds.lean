import PoincareConjecture.Proofs.M35.RadialGauge.SourceHighestJet
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelHigherGain
import PoincareConjecture.Proofs.M35.RadialGauge.PicardRegularity
import PoincareConjecture.Proofs.M35.RadialGauge.SmoothLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem exists_common_smooth_gauge_time {eta S K H T : ℝ}
    (heta : 0 < eta) (hS : 0 ≤ S) (hK : 0 ≤ K) (hH : 0 ≤ H) (hT : 0 < T) :
    ∃ t : ℝ, 0 < t ∧ t ≤ T ∧ S * heatC1Gain (n + 1) t ≤ eta ∧
      K * heatC1Gain (n + 1) t ≤ 1 / 4 ∧
      H * (2 * gaussianFirstMoment (n + 1) * Real.sqrt t) ≤ 1 / 2 := by
  obtain ⟨t, ht, htT, hball, hsmall⟩ :=
    exists_short_time_gauge_constants (n := n) heta hS
      (show 0 ≤ 2 * K + H by positivity) hT
  have hg := heatC1Gain_nonneg (n := n + 1) ht.le
  have hk := mul_le_mul_of_nonneg_right
    (show 2 * K ≤ 2 * K + H from le_add_of_nonneg_right hH) hg
  have hh := mul_le_mul_of_nonneg_right
    (show H ≤ 2 * K + H by linarith only [hK]) hg
  have hgain : 2 * gaussianFirstMoment (n + 1) * Real.sqrt t ≤ heatC1Gain (n + 1) t :=
    (le_add_of_nonneg_right (mul_nonneg gaussianSecondMoment_nonneg ht.le)).trans
      (le_max_right _ _)
  refine ⟨t, ht, htT, hball, ?_, ?_⟩
  · nlinarith only [hk, hsmall]
  · exact (mul_le_mul_of_nonneg_left hgain hH).trans (hh.trans hsmall)

theorem gaugePicard_uniform_all_order_bounds
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T eta B : ℝ}
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hcontrol : ∀ k, PicardSlabControl T eta (gaugePicard b G k))
    (hbm : StronglyMeasurable (fun p : Icc 0 T × V => b p.1.1 p.2))
    (hGm : Measurable (fun p : (Icc 0 T × V) × ℝ => G p.1.1.1 p.1.2 p.2))
    (hbs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (b s))
    (hGs : ∀ s ∈ Icc 0 T, ContDiff ℝ ∞ (fun p : V × ℝ => G s p.1 p.2))
    (hbb : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      ‖iteratedFDeriv ℝ j (b s) x‖ ≤ C)
    (hGb : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      ‖iteratedFDeriv ℝ j (fun p : V × ℝ => G s p.1 p.2) (x, z)‖ ≤ C)
    (hb : ∀ s ∈ Icc 0 T, ∀ x, ‖b s x‖ ≤ B)
    (hsmall : (B + 2 * (n + 1 : ℕ) * eta) *
      (2 * gaussianFirstMoment (n + 1) * Real.sqrt T) ≤ 1 / 2) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k t, t ∈ Icc 0 T → ∀ x,
      ‖iteratedFDeriv ℝ j (gaugePicard b G k t) x‖ ≤ C := by
  have huvalue (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : V) :
      |gaugePicard b G k t x| ≤ eta := by
    have hw := (hcontrol k).weighted t ht x |>.1
    rw [Real.norm_eq_abs] at hw
    nlinarith only [hw, mul_nonneg (norm_nonneg x) (abs_nonneg (gaugePicard b G k t x))]
  have hup (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : V) :
      ‖fderiv ℝ (gaugePicard b G k t) x‖ ≤ eta := by
    have hw := (hcontrol k).weighted t ht x |>.2
    nlinarith only [hw,
      mul_nonneg (norm_nonneg x) (norm_nonneg (fderiv ℝ (gaugePicard b G k t) x))]
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero =>
          exact ⟨eta, heta, fun k t ht x => by
            simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using huvalue k t ht x⟩
      | succ j =>
          by_cases hj : j = 0
          · subst j
            exact ⟨eta, heta, fun k t ht x => by
              change ‖iteratedFDeriv ℝ 1 (gaugePicard b G k t) x‖ ≤ eta
              rw [norm_iteratedFDeriv_one]
              exact hup k t ht x⟩
          have hpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
          let A := ℕ × Icc (0 : ℝ) T
          obtain ⟨C, hC, hsource⟩ := gaugeSource_highest_jet_bound
            (b := fun a : A => b a.2.1) (G := fun a : A => G a.2.1)
            (u := fun a : A => gaugePicard b G a.1 a.2.1) heta j hpos
            (fun a => hbs a.2.1 a.2.2) (fun a => hGs a.2.1 a.2.2)
            (fun a => (hcontrol a.1).smooth a.2.1 a.2.2)
            (fun a => huvalue a.1 a.2.1 a.2.2) (fun a => hup a.1 a.2.1 a.2.2)
            (fun a => hb a.2.1 a.2.2)
            (fun l => by
              obtain ⟨D, hD⟩ := hbb l
              exact ⟨D, fun a => hD a.2.1 a.2.2⟩)
            (fun l hl => by
              obtain ⟨D, _, hD⟩ := ih l (by omega)
              exact ⟨D, fun a => hD a.1 a.2.1 a.2.2⟩)
            (fun l => by
              obtain ⟨D, hD⟩ := hGb l
              exact ⟨D, fun a => hD a.2.1 a.2.2⟩)
          let K := B + 2 * (n + 1 : ℕ) * eta
          let gain := 2 * gaussianFirstMoment (n + 1) * Real.sqrt T
          let H := 2 * C * gain
          have hK : 0 ≤ K := by dsimp [K]; positivity
          have hgain : 0 ≤ gain := by
            dsimp [gain]
            exact mul_nonneg (mul_nonneg (by norm_num) gaussianFirstMoment_nonneg)
              (Real.sqrt_nonneg _)
          have hH : 0 ≤ H := by dsimp [H]; positivity
          have hstep : (K * H + C) * gain ≤ H := by
            have hs := mul_le_mul_of_nonneg_right hsmall hH
            change K * gain * H ≤ (1 / 2) * H at hs
            dsimp [H] at hs ⊢
            nlinarith only [hs]
          refine ⟨H, hH, ?_⟩
          intro k
          induction k with
          | zero =>
              intro t ht x
              simpa only [gaugePicard, iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
                using hH
          | succ k hk =>
              obtain ⟨hsm, hss, hsb⟩ :=
                (hcontrol k).source hT hbm hGm hbs hGs hbb hGb
              intro t ht x
              have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
              have hsm' : StronglyMeasurable (fun p : Icc 0 t × V =>
                  gaugeSource (b p.1.1) (G p.1.1) (gaugePicard b G k p.1.1) p.2) :=
                hsm.comp_measurable
                  (g := fun p : Icc 0 t × V =>
                    ((⟨p.1.1, hsub p.1.2⟩ : Icc 0 T), p.2)) (by fun_prop)
              have h := heatDuhamel_iteratedFDeriv_gain j ht.1
                (show 0 ≤ K * H + C by positivity) hsm'
                (fun s hs => hss s (hsub hs))
                (fun l => by
                  obtain ⟨D, hD⟩ := hsb l
                  exact ⟨D, fun s hs => hD s (hsub hs)⟩)
                (fun s hs y => (hsource (k, ⟨s, hsub hs⟩) y).trans
                  (add_le_add (mul_le_mul_of_nonneg_left (hk s (hsub hs) y) hK) (le_refl C))) x
              apply h.trans
              apply le_trans _ hstep
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.2)
                (mul_nonneg (by norm_num) gaussianFirstMoment_nonneg)

theorem gaugePicard_limit_contDiff_infty
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T eta : ℝ}
    {u : ℝ → V → ℝ}
    (hcontrol : ∀ k, PicardSlabControl T eta (gaugePicard b G k))
    (hb : ∀ j : ℕ, ∃ C : ℝ, ∀ k t, t ∈ Icc 0 T → ∀ x,
      ‖iteratedFDeriv ℝ j (gaugePicard b G k t) x‖ ≤ C)
    (hu : ∀ t ∈ Icc 0 T, ∀ x,
      Tendsto (fun k => gaugePicard b G k t x) atTop (𝓝 (u t x))) :
    ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (u t) := by
  intro t ht
  apply contDiff_limit_of_uniform_all_order_bounds
    (fun k => (hcontrol k).smooth t ht) _ (hu t ht)
  intro j
  obtain ⟨C, hC⟩ := hb j
  exact ⟨C, fun k => hC k t ht⟩

end PoincareConjecture.M35.RadialGauge
