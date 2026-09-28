import PoincareConjecture.Proofs.M35.RadialGauge.PicardHessian
import PoincareConjecture.Proofs.M35.RadialGauge.SourceHessian
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelThirdJets

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))
local notation "D" => V →L[ℝ] ℝ

noncomputable local instance m35PicardThirdBoundLocal1 :
    NormedAddCommGroup D := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35PicardThirdBoundLocal2 :
    NormedSpace ℝ D := ContinuousLinearMap.toNormedSpace

theorem gaugePicard_weighted_third_derivative_bound
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T eta B B1 B2 L1 M2 C2 H : ℝ}
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B) (hB1 : 0 ≤ B1)
    (hB2 : 0 ≤ B2) (hL1 : 0 ≤ L1) (hM2 : 0 ≤ M2) (hC2 : 0 ≤ C2) (hH : 0 ≤ H)
    (hcontrol : ∀ k, PicardSlabControl T eta (gaugePicard b G k))
    (hHess : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x‖ ≤ H)
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
    (hddb : ∀ s ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (fderiv ℝ (b s)) x‖ ≤ B2)
    (hGz : ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta → |forcingScalarDeriv (G s) x z| ≤ L1)
    (hGxx : ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta → (1 + ‖x‖) *
      ‖(fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv (G s) p.1 p.2) (x, z)).comp
        (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤ C2)
    (hGxz : ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      ‖fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv (G s) p.1 p.2) (x, z) (0, 1)‖ ≤ M2)
    (hGzx : ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      ‖(fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv (G s) p.1 p.2) (x, z)).comp
        (ContinuousLinearMap.inl ℝ V ℝ)‖ ≤ M2)
    (hGzz : ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      ‖fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv (G s) p.1 p.2) (x, z) (0, 1)‖ ≤ M2)
    (hsmall : (B + 2 * eta) * heatC1Gain (n + 1) T ≤ 1 / 2) :
    ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k t))) x‖ ≤
        2 * ((2 * B1 + 2 * H + L1) * H + (B2 + 2 * M2 + M2 * eta) * eta + C2) *
          heatC1Gain (n + 1) T := by
  let K := B + 2 * eta
  let Q := (2 * B1 + 2 * H + L1) * H + (B2 + 2 * M2 + M2 * eta) * eta + C2
  let J := 2 * Q * heatC1Gain (n + 1) T
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact mul_nonneg (by positivity) (heatC1Gain_nonneg hT)
  have hstep : (K * J + Q) * heatC1Gain (n + 1) T ≤ J := by
    have hs := mul_le_mul_of_nonneg_right hsmall hJ
    change K * heatC1Gain (n + 1) T * J ≤ (1 / 2) * J at hs
    dsimp [J] at hs ⊢
    nlinarith only [hs]
  intro k
  induction k with
  | zero =>
      intro t ht x
      simp only [gaugePicard, fderiv_fun_const, fderiv_zero, Pi.zero_apply]
      change (1 + ‖x‖) * ‖(0 : V →L[ℝ] (V →L[ℝ] D))‖ ≤ _
      rw [ContinuousLinearMap.opNorm_zero, mul_zero]
      exact hJ
  | succ k ih =>
      obtain ⟨hsm, hss, hsb⟩ := (hcontrol k).source hT hbm hGm hbs hGs hbb hGb
      intro t ht x
      have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
      have hsm' : StronglyMeasurable (fun p : Icc 0 t × V =>
          gaugeSource (b p.1.1) (G p.1.1) (gaugePicard b G k p.1.1) p.2) :=
        hsm.comp_measurable
          (g := fun p : Icc 0 t × V =>
            ((⟨p.1.1, hsub p.1.2⟩ : Icc 0 T), p.2)) (by fun_prop)
      have h := heatDuhamel_weighted_third_derivative_bound ht.1
        (show 0 ≤ K * J + Q by positivity) hsm'
        (fun s hs => hss s (hsub hs))
        (fun j => by
          obtain ⟨C, hC⟩ := hsb j
          exact ⟨C, fun s hs => hC s (hsub hs)⟩)
        (fun s hs y => by
          have hsT := hsub hs
          have hw := (hcontrol k).weighted s hsT y
          have huv : |gaugePicard b G k s y| ≤ eta := by
            have hvalue := hw.1
            rw [Real.norm_eq_abs] at hvalue
            nlinarith [mul_nonneg (norm_nonneg y) (abs_nonneg (gaugePicard b G k s y))]
          simpa only [K, J, Q, add_assoc] using
            gaugeSource_weighted_hessian_bound heta hB hB1 hB2 hL1 hM2 hH
              (hbs s hsT) (hGs s hsT) ((hcontrol k).smooth s hsT)
              (hb s hsT y) (hdb s hsT y) (hddb s hsT y)
              (hGz s hsT y _ huv) (hGxx s hsT y _ huv) (hGxz s hsT y _ huv)
              (hGzx s hsT y _ huv) (hGzz s hsT y _ huv) hw.2
              (hHess k s hsT y) (ih s hsT y)) x
      exact h.trans ((mul_le_mul_of_nonneg_left (heatC1Gain_mono (n := n + 1) ht.1 ht.2)
        (show 0 ≤ K * J + Q by positivity)).trans hstep)

end PoincareConjecture.M35.RadialGauge
