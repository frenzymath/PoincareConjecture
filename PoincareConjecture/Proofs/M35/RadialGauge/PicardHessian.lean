import PoincareConjecture.Proofs.M35.RadialGauge.PicardRegularity
import PoincareConjecture.Proofs.M35.RadialGauge.SourceDerivative
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))




theorem gaugePicard_weighted_hessian_bound
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T eta B B1 L1 C1 : ℝ}
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B) (hB1 : 0 ≤ B1)
    (hL1 : 0 ≤ L1) (hC1 : 0 ≤ C1)
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
    (hdb : ∀ s ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (b s) x‖ ≤ B1)
    (hGx : ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      (1 + ‖x‖) * ‖(fderiv ℝ (fun p : V × ℝ => G s p.1 p.2) (x, z)).comp
        (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤ C1)
    (hGz : ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      |fderiv ℝ (fun p : V × ℝ => G s p.1 p.2) (x, z) (0, 1)| ≤ L1)
    (hsmall : (B + 2 * eta) * heatC1Gain (n + 1) T ≤ 1 / 2) :
    ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x‖ ≤
        2 * ((B1 + L1) * eta + C1) * heatC1Gain (n + 1) T := by
  let K := B + 2 * eta
  let Q := (B1 + L1) * eta + C1
  let H := 2 * Q * heatC1Gain (n + 1) T
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hH : 0 ≤ H := by dsimp [H]; exact mul_nonneg (by positivity) (heatC1Gain_nonneg hT)
  have hstep : (K * H + Q) * heatC1Gain (n + 1) T ≤ H := by
    have hs := mul_le_mul_of_nonneg_right hsmall hH
    change K * heatC1Gain (n + 1) T * H ≤ (1 / 2) * H at hs
    dsimp [H] at hs ⊢
    nlinarith
  intro k
  induction k with
  | zero =>
      intro t ht x
      simp only [gaugePicard, fderiv_fun_const, fderiv_zero, Pi.zero_apply]
      change (1 + ‖x‖) * ‖(0 : V →L[ℝ] (V →L[ℝ] ℝ))‖ ≤ _
      rw [ContinuousLinearMap.opNorm_zero, mul_zero]
      exact hH
  | succ k ih =>
      obtain ⟨hsm, hss, hsb⟩ :=
        (hcontrol k).source hT hbm hGm hbs hGs hbb hGb
      intro t ht x
      have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
      have hsm' : StronglyMeasurable (fun p : Icc 0 t × V =>
          gaugeSource (b p.1.1) (G p.1.1) (gaugePicard b G k p.1.1) p.2) :=
        hsm.comp_measurable
          (g := fun p : Icc 0 t × V =>
            ((⟨p.1.1, hsub p.1.2⟩ : Icc 0 T), p.2)) (by fun_prop)
      have h := heatDuhamel_weighted_hessian_bound ht.1
        (show 0 ≤ K * H + Q by positivity) hsm'
        (fun s hs => hss s (hsub hs))
        (fun j => by
          obtain ⟨C, hC⟩ := hsb j
          exact ⟨C, fun s hs => hC s (hsub hs)⟩)
        (fun s hs y => by
          have hsT := hsub hs
          have hus := (hcontrol k).smooth s hsT
          have hw := (hcontrol k).weighted s hsT y
          have huv : |gaugePicard b G k s y| ≤ eta := by
            have hvalue := hw.1
            rw [Real.norm_eq_abs] at hvalue
            nlinarith [mul_nonneg (norm_nonneg y) (abs_nonneg (gaugePicard b G k s y))]
          simpa only [K, H, Q, add_assoc] using gaugeSource_weighted_fderiv_bound heta hB hB1 hL1
            ((hbs s hsT).differentiable (by simp) y) (hus.differentiable (by simp) y)
            ((contDiff_infty_iff_fderiv.mp hus).2.differentiable (by simp) y)
            ((hGs s hsT).differentiable (by simp) (y, gaugePicard b G k s y))
            (hb s hsT y) (hdb s hsT y) hw.2 (ih s hsT y)
            (hGx s hsT y _ huv) (hGz s hsT y _ huv)) x
      exact h.trans ((mul_le_mul_of_nonneg_left (heatC1Gain_mono ht.1 ht.2)
        (show 0 ≤ K * H + Q by positivity)).trans hstep)

end PoincareConjecture.M35.RadialGauge
