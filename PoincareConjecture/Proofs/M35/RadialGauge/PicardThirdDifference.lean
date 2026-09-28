import PoincareConjecture.Proofs.M35.RadialGauge.PicardThirdBound
import PoincareConjecture.Proofs.M35.RadialGauge.SourceHessianWeightedDifference









set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))
local notation "D" => V →L[ℝ] ℝ

noncomputable local instance m35PicardThirdDifferenceLocal1 :
    NormedAddCommGroup D := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35PicardThirdDifferenceLocal2 :
    NormedSpace ℝ D := ContinuousLinearMap.toNormedSpace
noncomputable local instance m35PicardThirdDifferenceLocal3 :
    NormedAddCommGroup (V →L[ℝ] D) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance m35PicardThirdDifferenceLocal4 :
    NormedSpace ℝ (V →L[ℝ] D) := ContinuousLinearMap.toNormedSpace

theorem gaugePicard_weighted_third_derivative_geometric
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T eta B B1 B2 L1 M2 M3 C2 H J D0 : ℝ}
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hL1 : 0 ≤ L1) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (hC2 : 0 ≤ C2)
    (hH : 0 ≤ H) (hJ : 0 ≤ J) (hD0 : 0 ≤ D0)
    (hcontrol : ∀ k, PicardSlabControl T eta (gaugePicard b G k))
    (hstep : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖gaugePicard b G (k + 1) t x - gaugePicard b G k t x‖ ≤ D0 * (1 / 2 : ℝ) ^ k ∧
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G (k + 1) t) x -
        fderiv ℝ (gaugePicard b G k t) x‖ ≤ D0 * (1 / 2 : ℝ) ^ k ∧
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G (k + 1) t)) x -
        fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x‖ ≤ D0 * (1 / 2 : ℝ) ^ k)
    (hHess : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x‖ ≤ H)
    (hThird : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k t))) x‖ ≤ J)
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
    (hGzlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |forcingScalarDeriv (G s) x a - forcingScalarDeriv (G s) x c| ≤ M2 * |a - c|)
    (hDGxlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      ‖fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv (G s) p.1 p.2) (x, a) -
        fderiv ℝ (fun p : V × ℝ => forcingSpaceDeriv (G s) p.1 p.2) (x, c)‖ ≤ M3 * |a - c|)
    (hDGzlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      ‖fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv (G s) p.1 p.2) (x, a) -
        fderiv ℝ (fun p : V × ℝ => forcingScalarDeriv (G s) p.1 p.2) (x, c)‖ ≤ M3 * |a - c|)
    (hsmall : (B + 2 * eta) * heatC1Gain (n + 1) T ≤ 1 / 4) :
    ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G (k + 1) t))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (gaugePicard b G k t))) x‖ ≤
      (J + 4 * (2 * B1 + 4 * H + L1 + B2 + 2 * J + 2 * M2 * (1 + eta) +
        M3 * (1 + eta) ^ 2 + M2 * H) * D0 * heatC1Gain (n + 1) T) * (1 / 2 : ℝ) ^ k := by
  let K := B + 2 * eta
  let A := 2 * B1 + 4 * H + L1 + B2 + 2 * J + 2 * M2 * (1 + eta) +
    M3 * (1 + eta) ^ 2 + M2 * H
  let M := J + 4 * A * D0 * heatC1Gain (n + 1) T
  let S := K * J + (2 * B1 + 2 * H + L1) * H + (B2 + 2 * M2 + M2 * eta) * eta + C2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg hJ (mul_nonneg (by positivity) (heatC1Gain_nonneg hT))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hJM : J ≤ M := by
    dsimp [M]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (heatC1Gain_nonneg hT))
  have hvalue (k : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) :
      |gaugePicard b G k s x| ≤ eta := by
    have h := ((hcontrol k).weighted s hs x).1
    rw [Real.norm_eq_abs] at h
    nlinarith [mul_nonneg (norm_nonneg x) (abs_nonneg (gaugePicard b G k s x))]
  have hsource (k : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) :
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G k s))) x‖ ≤ S :=
    gaugeSource_weighted_hessian_bound heta hB hB1 hB2 hL1 hM2 hH
      (hbs s hs) (hGs s hs) ((hcontrol k).smooth s hs)
      (hb s hs x) (hdb s hs x) (hddb s hs x) (hGz s hs x _ (hvalue k s hs x))
      (hGxx s hs x _ (hvalue k s hs x)) (hGxz s hs x _ (hvalue k s hs x))
      (hGzx s hs x _ (hvalue k s hs x)) (hGzz s hs x _ (hvalue k s hs x))
      ((hcontrol k).weighted s hs x).2 (hHess k s hs x) (hThird k s hs x)
  intro k
  induction k with
  | zero =>
      intro t ht x
      have h := (hThird 1 t ht x).trans hJM
      simpa only [gaugePicard, fderiv_fun_const, fderiv_zero, Pi.zero_apply,
        sub_zero, pow_zero, mul_one] using h
  | succ k ih =>
      obtain ⟨hfm, hfs, hfb⟩ := (hcontrol (k + 1)).source hT hbm hGm hbs hGs hbb hGb
      obtain ⟨hgm, hgs, hgb⟩ := (hcontrol k).source hT hbm hGm hbs hGs hbb hGb
      intro t ht x
      have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
      have hm (j : ℕ) (hmj : StronglyMeasurable (fun p : Icc 0 T × V =>
          gaugeSource (b p.1.1) (G p.1.1) (gaugePicard b G j p.1.1) p.2)) :
          StronglyMeasurable (fun p : Icc 0 t × V =>
            gaugeSource (b p.1.1) (G p.1.1) (gaugePicard b G j p.1.1) p.2) :=
        hmj.comp_measurable
          (g := fun p : Icc 0 t × V => ((⟨p.1.1, hsub p.1.2⟩ : Icc 0 T), p.2)) (by fun_prop)
      have hdiff (s : ℝ) (hs : s ∈ Icc 0 t) (y : V) :
          (1 + ‖y‖) *
            ‖fderiv ℝ (fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G (k + 1) s))) y -
              fderiv ℝ (fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G k s))) y‖ ≤
            K * (M * (1 / 2 : ℝ) ^ k) + A * (D0 * (1 / 2 : ℝ) ^ k) := by
        have hsT := hsub hs
        exact gaugeSource_weighted_hessian_difference_bound heta hB hB1 hB2 hL1 hM2 hM3 hH hJ
          (hbs s hsT) (hGs s hsT) ((hcontrol (k + 1)).smooth s hsT) ((hcontrol k).smooth s hsT)
          (hb s hsT y) (hdb s hsT y) (hddb s hsT y)
          (hGz s hsT y _ (hvalue (k + 1) s hsT y))
          (hGxz s hsT y _ (hvalue k s hsT y)) (hGzx s hsT y _ (hvalue (k + 1) s hsT y))
          (hGzz s hsT y _ (hvalue (k + 1) s hsT y)) (hGzz s hsT y _ (hvalue k s hsT y))
          (hGzlip s hsT y _ _ (hvalue (k + 1) s hsT y) (hvalue k s hsT y))
          (hDGxlip s hsT y _ _ (hvalue (k + 1) s hsT y) (hvalue k s hsT y))
          (hDGzlip s hsT y _ _ (hvalue (k + 1) s hsT y) (hvalue k s hsT y))
          ((hcontrol (k + 1)).weighted s hsT y).2 ((hcontrol k).weighted s hsT y).2
          (hHess (k + 1) s hsT y) (hHess k s hsT y) (hThird k s hsT y)
          (by simpa only [Real.norm_eq_abs] using (hstep k s hsT y).1)
          (hstep k s hsT y).2.1 (hstep k s hsT y).2.2 (ih s hsT y)
      have h := heatDuhamel_weighted_third_derivative_difference_bound ht.1 hS hS
        (show 0 ≤ K * (M * (1 / 2 : ℝ) ^ k) + A * (D0 * (1 / 2 : ℝ) ^ k) by positivity)
        (hm (k + 1) hfm) (hm k hgm) (fun s hs => hfs s (hsub hs)) (fun s hs => hgs s (hsub hs))
        (fun j => by
          obtain ⟨C, hC⟩ := hfb j
          exact ⟨C, fun s hs => hC s (hsub hs)⟩)
        (fun j => by
          obtain ⟨C, hC⟩ := hgb j
          exact ⟨C, fun s hs => hC s (hsub hs)⟩)
        (fun s hs => hsource (k + 1) s (hsub hs)) (fun s hs => hsource k s (hsub hs)) hdiff x
      have htime : (K * M + A * D0) * heatC1Gain (n + 1) t ≤
          (K * M + A * D0) * heatC1Gain (n + 1) T :=
        mul_le_mul_of_nonneg_left (heatC1Gain_mono (n := n + 1) ht.1 ht.2)
          (show 0 ≤ K * M + A * D0 by positivity)
      have hhigh := mul_le_mul_of_nonneg_right hsmall hM
      change K * heatC1Gain (n + 1) T * M ≤ (1 / 4) * M at hhigh
      have hlower : A * D0 * heatC1Gain (n + 1) T ≤ (1 / 4) * M := by
        dsimp [M]
        nlinarith only [hJ]
      have hwhole : (K * M + A * D0) * heatC1Gain (n + 1) t ≤ (1 / 2) * M := by
        nlinarith only [htime, hhigh, hlower]
      have hp := mul_le_mul_of_nonneg_right hwhole (show 0 ≤ (1 / 2 : ℝ) ^ k by positivity)
      have hgain : (K * (M * (1 / 2 : ℝ) ^ k) + A * (D0 * (1 / 2 : ℝ) ^ k)) *
          heatC1Gain (n + 1) t ≤ M * (1 / 2 : ℝ) ^ (k + 1) := by
        rw [pow_succ]
        nlinarith only [hp]
      exact h.trans hgain

end PoincareConjecture.M35.RadialGauge
