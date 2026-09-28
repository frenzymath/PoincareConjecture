import PoincareConjecture.Proofs.M35.RadialGauge.RadialNormJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M35.RadialGauge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem even_radial_weighted_jets {f : ℝ → ℝ} {N : ℕ} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f)
    (hweighted : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j f r| ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E,
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ k (fun y : E => f ‖y‖) x‖ ≤ C := by
  classical
  let F : E → ℝ := fun x => f ‖x‖
  have hF : ContDiff ℝ ∞ F := SmoothRadial.contDiff_even_norm hf he
  intro k
  obtain ⟨D, hD, hDb⟩ := norm_unit_sphere_jet_bounds (E := E) k
  choose B hB0 hB using hweighted
  let B' := 1 + ∑ i ∈ Finset.range (k + 1), B i
  have hB' : 0 < B' := by
    have := Finset.sum_nonneg (s := Finset.range (k + 1)) (fun i _ => hB0 i)
    dsimp only [B']
    linarith
  let Cfar := (k.factorial : ℝ) * B' * D ^ k
  have hCfar : 0 ≤ Cfar := by dsimp only [Cfar]; positivity
  have hfar (x : E) (hx : 1 ≤ ‖x‖) :
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ k F x‖ ≤ Cfar := by
    let R := ‖x‖
    let z := R⁻¹ • x
    have hR : 0 < R := lt_of_lt_of_le zero_lt_one hx
    have hz : ‖z‖ = 1 := by
      simp only [z, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR]
      exact inv_mul_cancel₀ hR.ne'
    have hRz : R • z = x := by
      dsimp only [z]
      rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    let S := ({0} : Set E)ᶜ
    have hS : IsOpen S := isClosed_singleton.isOpen_compl
    have hzS : z ∈ S := by
      change z ≠ 0
      intro hzero
      simp only [hzero, norm_zero, zero_ne_one] at hz
    have hn : ContDiffOn ℝ ∞ (fun y : E => ‖y‖) S := by
      intro y hy
      exact (contDiffAt_id.norm ℝ (show y ≠ 0 from hy)).contDiffWithinAt
    let fR : ℝ → ℝ := fun r => f (R * r)
    have hfR : ContDiff ℝ ∞ fR := hf.comp (contDiff_const.mul contDiff_id)
    have houter (i : ℕ) (hi : i ≤ k) :
        ‖iteratedFDerivWithin ℝ i fR univ ‖z‖‖ ≤ B' * R ^ k / (1 + R) ^ N := by
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      have hid := congrFun (iteratedDeriv_comp_const_mul
        (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)) R) ‖z‖
      change iteratedDeriv i fR ‖z‖ = _ at hid
      rw [hid, hz, mul_one, abs_mul, abs_pow, abs_of_pos hR]
      apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + R) N)).mpr
      have hBi : B i ≤ B' := by
        have hh := Finset.single_le_sum (f := B) (fun i _ => hB0 i)
          (show i ∈ Finset.range (k + 1) by
            simpa only [Finset.mem_range] using Nat.lt_succ_of_le hi)
        dsimp only [B']
        linarith
      have hpower : R ^ i ≤ R ^ k := pow_le_pow_right₀ hx hi
      have hm := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpower
          (pow_nonneg (by positivity : 0 ≤ 1 + R) N)) (abs_nonneg (iteratedDeriv i f R))
      have hlast := mul_le_mul_of_nonneg_left ((hB i R hx).trans hBi) (pow_nonneg hR.le k)
      nlinarith only [hm, hlast]
    have hinner (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
        ‖iteratedFDerivWithin ℝ i (fun y : E => ‖y‖) S z‖ ≤ D ^ i := by
      rw [iteratedFDerivWithin_of_isOpen i hS hzS]
      exact (hDb i hik z hz).trans (le_self_pow₀ hD (by omega))
    have hcomp := norm_iteratedFDerivWithin_comp_le hfR.contDiffOn hn
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k) uniqueDiffOn_univ hS.uniqueDiffOn
      (fun _ _ => mem_univ _) hzS houter hinner
    rw [iteratedFDerivWithin_of_isOpen k hS hzS] at hcomp
    have hfunctions : (fun y : E => F (R • y)) = fR ∘ (fun y : E => ‖y‖) := by
      funext y
      simp only [F, fR, Function.comp_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hscale := congrFun (iteratedFDeriv_comp_const_smul R
      (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k))) z
    rw [hfunctions, hRz] at hscale
    have hnorm := congrArg norm hscale
    rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hR] at hnorm
    rw [hnorm] at hcomp
    have hh := mul_le_mul_of_nonneg_left hcomp
      (pow_nonneg (by positivity : 0 ≤ 1 + R) N)
    have hcancel : (1 + R) ^ N *
        ((k.factorial : ℝ) * (B' * R ^ k / (1 + R) ^ N) * D ^ k) = R ^ k * Cfar := by
      dsimp only [Cfar]
      field_simp [show 1 + R ≠ 0 by positivity]
    have hmul := hh.trans_eq hcancel
    rw [show (1 + R) ^ N * (R ^ k * ‖iteratedFDeriv ℝ k F x‖) =
      R ^ k * ((1 + R) ^ N * ‖iteratedFDeriv ℝ k F x‖) by ring] at hmul
    exact (mul_le_mul_iff_right₀ (pow_pos hR k)).mp hmul
  obtain ⟨Bnear, hnear⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    ((hF.continuous_iteratedFDeriv (m := k)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).continuousOn)
  let Cnear := (2 : ℝ) ^ N * max Bnear 0
  have hCnear : 0 ≤ Cnear := by dsimp only [Cnear]; positivity
  refine ⟨Cfar + Cnear, add_nonneg hCfar hCnear, ?_⟩
  intro x
  by_cases hx : 1 ≤ ‖x‖
  · exact (hfar x hx).trans (le_add_of_nonneg_right hCnear)
  · have hx1 : ‖x‖ ≤ 1 := le_of_lt (lt_of_not_ge hx)
    have hmem : x ∈ Metric.closedBall (0 : E) 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx1
    have hh := mul_le_mul
      (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖) (by linarith only [hx1]) N)
      ((hnear x hmem).trans (le_max_left Bnear 0)) (norm_nonneg _)
      (by positivity : 0 ≤ (2 : ℝ) ^ N)
    exact hh.trans (le_add_of_nonneg_left hCfar)

theorem even_radial_rapid_jets {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (he : Function.Even f)
    (hrapid : ∀ j N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j f r| ≤ C) :
    ∀ k N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E,
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ k (fun y : E => f ‖y‖) x‖ ≤ C := by
  intro k N
  exact even_radial_weighted_jets hf he (fun j => hrapid j N) k

end PoincareConjecture.M35.RadialGauge
