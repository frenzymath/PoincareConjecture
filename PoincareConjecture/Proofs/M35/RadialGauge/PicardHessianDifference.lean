import PoincareConjecture.Proofs.M35.RadialGauge.PicardHessian
import PoincareConjecture.Proofs.M35.RadialGauge.SourceDerivativeDifference
import PoincareConjecture.Proofs.M35.RadialGauge.DuhamelHessianDifference










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))




theorem gaugePicard_weighted_hessian_geometric
    {b : ℝ → V → V} {G : ℝ → V → ℝ → ℝ} {T eta B B1 L1 C1 Lx Lz H : ℝ}
    (hT : 0 ≤ T) (heta : 0 ≤ eta) (hB : 0 ≤ B) (hB1 : 0 ≤ B1)
    (hL1 : 0 ≤ L1) (hC1 : 0 ≤ C1) (hLx : 0 ≤ Lx) (hLz : 0 ≤ Lz) (hH : 0 ≤ H)
    (hcontrol : ∀ k, PicardSlabControl T eta (gaugePicard b G k))
    (hstep : ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖gaugePicard b G (k + 1) t x - gaugePicard b G k t x‖ ≤
        eta * (1 / 2 : ℝ) ^ k ∧
      (1 + ‖x‖) * ‖fderiv ℝ (gaugePicard b G (k + 1) t) x -
        fderiv ℝ (gaugePicard b G k t) x‖ ≤ eta * (1 / 2 : ℝ) ^ k)
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
    (hGx : ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta →
      (1 + ‖x‖) * ‖forcingSpaceDeriv (G s) x z‖ ≤ C1)
    (hGz : ∀ s ∈ Icc 0 T, ∀ x z, |z| ≤ eta → |forcingScalarDeriv (G s) x z| ≤ L1)
    (hGxlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      ‖forcingSpaceDeriv (G s) x a - forcingSpaceDeriv (G s) x c‖ ≤ Lx * |a - c|)
    (hGzlip : ∀ s ∈ Icc 0 T, ∀ x a c, |a| ≤ eta → |c| ≤ eta →
      |forcingScalarDeriv (G s) x a - forcingScalarDeriv (G s) x c| ≤ Lz * |a - c|)
    (hsmall : (B + 2 * eta) * heatC1Gain (n + 1) T ≤ 1 / 4) :
    ∀ k t, t ∈ Icc 0 T → ∀ x,
      (1 + ‖x‖) * ‖fderiv ℝ (fderiv ℝ (gaugePicard b G (k + 1) t)) x -
        fderiv ℝ (fderiv ℝ (gaugePicard b G k t)) x‖ ≤
      (H + 4 * (B1 + 2 * H + L1 + Lx + Lz * eta) * eta * heatC1Gain (n + 1) T) *
        (1 / 2 : ℝ) ^ k := by
  let K := B + 2 * eta
  let A := B1 + 2 * H + L1 + Lx + Lz * eta
  let M := H + 4 * A * eta * heatC1Gain (n + 1) T
  let S := K * H + (B1 + L1) * eta + C1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hM : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg hH (mul_nonneg (by positivity) (heatC1Gain_nonneg hT))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hHM : H ≤ M := by
    dsimp [M]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (heatC1Gain_nonneg hT))
  have hvalue (k : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) :
      |gaugePicard b G k s x| ≤ eta := by
    have h := ((hcontrol k).weighted s hs x).1
    rw [Real.norm_eq_abs] at h
    nlinarith [mul_nonneg (norm_nonneg x) (abs_nonneg (gaugePicard b G k s x))]
  have hsource (k : ℕ) (s : ℝ) (hs : s ∈ Icc 0 T) (x : V) :
      (1 + ‖x‖) * ‖fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G k s)) x‖ ≤ S := by
    have hu := (hcontrol k).smooth s hs
    exact gaugeSource_weighted_fderiv_bound heta hB hB1 hL1
      ((hbs s hs).differentiable (by simp) x) (hu.differentiable (by simp) x)
      ((contDiff_infty_iff_fderiv.mp hu).2.differentiable (by simp) x)
      ((hGs s hs).differentiable (by simp) (x, gaugePicard b G k s x))
      (hb s hs x) (hdb s hs x) ((hcontrol k).weighted s hs x).2 (hHess k s hs x)
      (hGx s hs x _ (hvalue k s hs x)) (hGz s hs x _ (hvalue k s hs x))
  intro k
  induction k with
  | zero =>
      intro t ht x
      have h := (hHess 1 t ht x).trans hHM
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
          (1 + ‖y‖) * ‖fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G (k + 1) s)) y -
            fderiv ℝ (gaugeSource (b s) (G s) (gaugePicard b G k s)) y‖ ≤
          K * (M * (1 / 2 : ℝ) ^ k) + A * (eta * (1 / 2 : ℝ) ^ k) := by
        have hsT := hsub hs
        have hu := (hcontrol (k + 1)).smooth s hsT
        have hv := (hcontrol k).smooth s hsT
        exact gaugeSource_weighted_fderiv_sub_bound heta hB hB1 hL1 hH hLx hLz
          ((hbs s hsT).differentiable (by simp) y)
          (hu.differentiable (by simp) y) (hv.differentiable (by simp) y)
          ((contDiff_infty_iff_fderiv.mp hu).2.differentiable (by simp) y)
          ((contDiff_infty_iff_fderiv.mp hv).2.differentiable (by simp) y)
          ((hGs s hsT).differentiable (by simp) (y, gaugePicard b G (k + 1) s y))
          ((hGs s hsT).differentiable (by simp) (y, gaugePicard b G k s y))
          (hb s hsT y) (hdb s hsT y) (hGz s hsT y _ (hvalue (k + 1) s hsT y))
          (hGxlip s hsT y _ _ (hvalue (k + 1) s hsT y) (hvalue k s hsT y))
          (hGzlip s hsT y _ _ (hvalue (k + 1) s hsT y) (hvalue k s hsT y))
          ((hcontrol (k + 1)).weighted s hsT y).2 ((hcontrol k).weighted s hsT y).2
          (hHess k s hsT y) (ih s hsT y)
          (by simpa only [Real.norm_eq_abs] using (hstep k s hsT y).1) (hstep k s hsT y).2
      have h := heatDuhamel_weighted_hessian_difference_bound ht.1 hS hS
        (show 0 ≤ K * (M * (1 / 2 : ℝ) ^ k) + A * (eta * (1 / 2 : ℝ) ^ k) by positivity)
        (hm (k + 1) hfm) (hm k hgm) (fun s hs => hfs s (hsub hs))
        (fun s hs => hgs s (hsub hs))
        (fun j => by
          obtain ⟨C, hC⟩ := hfb j
          exact ⟨C, fun s hs => hC s (hsub hs)⟩)
        (fun j => by
          obtain ⟨C, hC⟩ := hgb j
          exact ⟨C, fun s hs => hC s (hsub hs)⟩)
        (fun s hs => hsource (k + 1) s (hsub hs))
        (fun s hs => hsource k s (hsub hs)) hdiff x
      have hgain : (K * (M * (1 / 2 : ℝ) ^ k) + A * (eta * (1 / 2 : ℝ) ^ k)) *
          heatC1Gain (n + 1) t ≤ M * (1 / 2 : ℝ) ^ (k + 1) := by
        have htime : (K * M + A * eta) * heatC1Gain (n + 1) t ≤
            (K * M + A * eta) * heatC1Gain (n + 1) T :=
          mul_le_mul_of_nonneg_left (heatC1Gain_mono (n := n + 1) ht.1 ht.2)
            (show 0 ≤ K * M + A * eta by positivity)
        have hhigh := mul_le_mul_of_nonneg_right hsmall hM
        change K * heatC1Gain (n + 1) T * M ≤ (1 / 4) * M at hhigh
        have hlower : A * eta * heatC1Gain (n + 1) T ≤ (1 / 4) * M := by
          dsimp [M]
          nlinarith
        have hwhole : (K * M + A * eta) * heatC1Gain (n + 1) t ≤ (1 / 2) * M := by
          nlinarith [htime, hhigh, hlower]
        have hp := mul_le_mul_of_nonneg_right hwhole
          (show 0 ≤ (1 / 2 : ℝ) ^ k by positivity)
        rw [pow_succ]
        nlinarith [hp]
      exact h.trans hgain

end PoincareConjecture.M35.RadialGauge
