import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SpectralSemigroup
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul











set_option autoImplicit false

noncomputable section

namespace Poincare.Analysis.Dirichlet.Spectral

open Filter
open scoped Topology InnerProductSpace NNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem pow_mul_exp_le (k : ℕ) {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a) :
    a ^ k * Real.exp (-a * t) ≤ (k.factorial : ℝ) / t ^ k := by
  have h := Real.pow_div_factorial_le_exp (a * t) (mul_nonneg ha ht.le) k
  have hfac : (0 : ℝ) < k.factorial := by positivity
  rw [div_le_iff₀ hfac] at h
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos (-(a * t))).le
  rw [mul_assoc, mul_comm (k.factorial : ℝ), ← mul_assoc,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h'
  apply (le_div_iff₀ (pow_pos ht k)).mpr
  calc
    a ^ k * Real.exp (-a * t) * t ^ k = (a * t) ^ k * Real.exp (-(a * t)) := by
      rw [mul_pow, neg_mul]; ring
    _ ≤ (k.factorial : ℝ) := h'

private theorem norm_weight_mul_le (lam : ι → ℝ≥0) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (i : ι) (r : ℝ) :
    ‖((lam i : ℝ) ^ k * Real.exp (-(lam i : ℝ) * t)) * r‖ ≤
      ((k.factorial : ℝ) / t ^ k) * ‖r‖ := by
  rw [norm_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (pow_mul_exp_le k ht (lam i).coe_nonneg) (norm_nonneg _)

theorem weighted_coeff_memLp (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (u : H) :
    Memℓp (fun i => (lam i : ℝ) ^ k * Real.exp (-(lam i : ℝ) * t) * b.repr u i) 2 := by
  apply ((b.repr u).property.norm.const_mul ((k.factorial : ℝ) / t ^ k)).mono
  exact fun i => norm_weight_mul_le lam k ht i _

private def powerMultiplier (lam : ι → ℝ≥0) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    lp (fun _ : ι => ℝ) 2 →L[ℝ] lp (fun _ : ι => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => (lam i : ℝ) ^ k * Real.exp (-(lam i : ℝ) * t) * x i,
        (x.property.norm.const_mul ((k.factorial : ℝ) / t ^ k)).mono
          (fun i => norm_weight_mul_le lam k ht i _)⟩
      map_add' := by
        intro x y; ext i
        change _ * (x i + y i) = _ * x i + _ * y i
        ring
      map_smul' := by
        intro r x; ext i
        change _ * (r * x i) = r * (_ * x i)
        ring }
    ((k.factorial : ℝ) / t ^ k) (fun x => by
      have hb : 0 ≤ (k.factorial : ℝ) / t ^ k := by positivity
      have hn := lp.norm_mono (p := 2) (by norm_num)
        (x := (⟨_, (x.property.norm.const_mul ((k.factorial : ℝ) / t ^ k)).mono
          (fun i => norm_weight_mul_le lam k ht i _)⟩ : lp (fun _ : ι => ℝ) 2))
        (y := ((k.factorial : ℝ) / t ^ k) • x) (fun i => by
          simpa [norm_smul, Real.norm_of_nonneg hb] using norm_weight_mul_le lam k ht i (x i))
      simpa [norm_smul, Real.norm_of_nonneg hb] using hn)


def heatPower (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (k : ℕ) (t : ℝ) : H →L[ℝ] H :=
  if ht : 0 < t then
    b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((powerMultiplier lam k t ht).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap)
  else 0

theorem heatPower_repr (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (u : H) (i : ι) :
    b.repr (heatPower b lam k t u) i =
      (lam i : ℝ) ^ k * Real.exp (-(lam i : ℝ) * t) * b.repr u i := by
  simp only [heatPower, dif_pos ht]
  change b.repr (b.repr.symm (powerMultiplier lam k t ht (b.repr u))) i = _
  rw [b.repr.apply_symm_apply]
  rfl

theorem heatPower_hasSum (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (u : H) :
    HasSum (fun i => ((lam i : ℝ) ^ k * Real.exp (-(lam i : ℝ) * t) * b.repr u i) • b i)
      (heatPower b lam k t u) := by
  simpa only [heatPower_repr b lam k ht] using b.hasSum_repr (heatPower b lam k t u)

theorem summable_weighted_coeff_sq (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (u : H) :
    Summable (fun i => ((lam i : ℝ) ^ k * Real.exp (-(lam i : ℝ) * t) * b.repr u i) ^ 2) := by
  simpa only [heatPower_repr b lam k ht] using summable_repr_sq b (heatPower b lam k t u)

private theorem norm_le_of_repr (b : HilbertBasis ι ℝ H) (u v : H) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖b.repr v i‖ ≤ C * ‖b.repr u i‖) : ‖v‖ ≤ C * ‖u‖ := by
  have hn := lp.norm_mono (p := 2) (by norm_num)
    (x := b.repr v) (y := C • b.repr u) (fun i => by
      simpa [norm_smul, Real.norm_of_nonneg hC] using h i)
  simpa [norm_smul, Real.norm_of_nonneg hC] using hn

theorem norm_heatPower_le (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (k : ℕ)
    {t : ℝ} (ht : 0 < t) : ‖heatPower b lam k t‖ ≤ (k.factorial : ℝ) / t ^ k := by
  apply (heatPower b lam k t).opNorm_le_bound (by positivity)
  intro u
  apply norm_le_of_repr b u _ (by positivity)
  intro i
  rw [heatPower_repr b lam k ht]
  exact norm_weight_mul_le lam k ht i _

theorem heatPower_zero_eq_heat (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0)
    {t : ℝ} (ht : 0 < t) : heatPower b lam 0 t = heat b lam t.toNNReal := by
  ext u
  apply b.repr.injective
  ext i
  simp [heatPower_repr b lam 0 ht, heat_repr, Real.coe_toNNReal _ ht.le]

private theorem exp_taylor_bound (s : ℝ) :
    |Real.exp s - 1 - s| ≤ s ^ 2 * Real.exp |s| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (s : ℂ) 2
  have heq : Complex.exp (s : ℂ) - (1 + (s : ℂ)) =
      ((Real.exp s - 1 - s : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp]
    push_cast
    ring
  have hsum : ∑ m ∈ Finset.range 2, (s : ℂ) ^ m / (m.factorial : ℂ) = 1 + (s : ℂ) := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum, heq, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs] at h
  exact h

private theorem scalar_taylor_bound (k : ℕ) {t h a : ℝ}
    (ht : 0 < t) (hh : |h| ≤ t / 2) (ha : 0 ≤ a) :
    |a ^ k * (Real.exp (-a * (t + h)) - Real.exp (-a * t) +
        a * h * Real.exp (-a * t))| ≤
      ((k + 2).factorial : ℝ) / (t / 2) ^ (k + 2) * h ^ 2 := by
  have hf : Real.exp (-a * (t + h)) - Real.exp (-a * t) +
      a * h * Real.exp (-a * t) =
      Real.exp (-a * t) * (Real.exp (-a * h) - 1 - (-a * h)) := by
    rw [mul_add, Real.exp_add]
    ring
  have htaylor := exp_taylor_bound (-a * h)
  rw [abs_mul, abs_neg, abs_of_nonneg ha, mul_pow, neg_sq] at htaylor
  have htime : t / 2 ≤ t - |h| := by linarith
  have hexp : Real.exp (-a * (t - |h|)) ≤ Real.exp (-a * (t / 2)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left htime (neg_nonpos.mpr ha)
  calc
    |a ^ k * (Real.exp (-a * (t + h)) - Real.exp (-a * t) +
        a * h * Real.exp (-a * t))| =
        a ^ k * Real.exp (-a * t) * |Real.exp (-a * h) - 1 - (-a * h)| := by
      rw [hf, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ha k),
        abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ a ^ k * Real.exp (-a * t) * (a ^ 2 * h ^ 2 * Real.exp (a * |h|)) :=
      mul_le_mul_of_nonneg_left htaylor (by positivity)
    _ = a ^ (k + 2) * Real.exp (-a * (t - |h|)) * h ^ 2 := by
      rw [show -a * (t - |h|) = -a * t + a * |h| by ring, Real.exp_add, pow_add]
      ring
    _ ≤ a ^ (k + 2) * Real.exp (-a * (t / 2)) * h ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (pow_nonneg ha _)) (sq_nonneg h)
    _ ≤ ((k + 2).factorial : ℝ) / (t / 2) ^ (k + 2) * h ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_mul_exp_le (k + 2) (by linarith) ha) (sq_nonneg h)

theorem norm_heatPower_taylor_remainder (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0)
    (k : ℕ) {t h : ℝ} (ht : 0 < t) (hh : |h| ≤ t / 2) :
    ‖heatPower b lam k (t + h) - heatPower b lam k t +
        h • heatPower b lam (k + 1) t‖ ≤
      ((k + 2).factorial : ℝ) / (t / 2) ^ (k + 2) * h ^ 2 := by
  have hth : 0 < t + h := by
    have := (abs_le.mp hh).1
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply norm_le_of_repr b u _ (by positivity)
  intro i
  change ‖b.repr (heatPower b lam k (t + h) u - heatPower b lam k t u +
    h • heatPower b lam (k + 1) t u) i‖ ≤ _
  simp only [map_add, map_sub, map_smul, lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    heatPower_repr b lam k hth, heatPower_repr b lam k ht,
    heatPower_repr b lam (k + 1) ht]
  have heq : (lam i : ℝ) ^ k * Real.exp (-(lam i : ℝ) * (t + h)) * b.repr u i -
        (lam i : ℝ) ^ k * Real.exp (-(lam i : ℝ) * t) * b.repr u i +
        h * ((lam i : ℝ) ^ (k + 1) * Real.exp (-(lam i : ℝ) * t) * b.repr u i) =
      ((lam i : ℝ) ^ k * (Real.exp (-(lam i : ℝ) * (t + h)) -
        Real.exp (-(lam i : ℝ) * t) +
        (lam i : ℝ) * h * Real.exp (-(lam i : ℝ) * t))) * b.repr u i := by
    rw [pow_succ]
    ring
  rw [heq, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (scalar_taylor_bound k ht hh (lam i).coe_nonneg)
    (norm_nonneg _)

theorem hasDerivAt_heatPower (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => heatPower b lam k s) (-heatPower b lam (k + 1) t) t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let C : ℝ := ((k + 2).factorial : ℝ) / (t / 2) ^ (k + 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hC1 : 0 < C + 1 := by positivity
  have hδ : 0 < min (t / 2) (ε / (C + 1)) :=
    lt_min (by linarith) (div_pos hε hC1)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, lt_min_iff] at hh
  have hbound := norm_heatPower_taylor_remainder b lam k ht hh.1.le
  rw [smul_neg, sub_neg_eq_add]
  apply le_trans hbound
  change C * h ^ 2 ≤ ε * ‖h‖
  rw [Real.norm_eq_abs, ← sq_abs, pow_two, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg h)
  have hsmall : |h| * (C + 1) < ε := (lt_div_iff₀ hC1).mp hh.2
  nlinarith [abs_nonneg h]

theorem hasDerivAt_heat (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => heat b lam s.toNNReal) (-heatPower b lam 1 t) t := by
  apply (hasDerivAt_heatPower b lam 0 ht).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact (heatPower_zero_eq_heat b lam hs).symm

theorem hasDerivAt_heatPower_apply (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0) (k : ℕ)
    {t : ℝ} (ht : 0 < t) (u : H) :
    HasDerivAt (fun s : ℝ => heatPower b lam k s u) (-heatPower b lam (k + 1) t u) t := by
  exact (hasDerivAt_heatPower b lam k ht).clm_apply (hasDerivAt_const t u)
    |>.congr_deriv (by simp)

theorem hasDerivAt_heat_apply (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0)
    {t : ℝ} (ht : 0 < t) (u : H) :
    HasDerivAt (fun s : ℝ => heat b lam s.toNNReal u) (-heatPower b lam 1 t u) t := by
  exact (hasDerivAt_heat b lam ht).clm_apply (hasDerivAt_const t u) |>.congr_deriv (by simp)

end Poincare.Analysis.Dirichlet.Spectral
