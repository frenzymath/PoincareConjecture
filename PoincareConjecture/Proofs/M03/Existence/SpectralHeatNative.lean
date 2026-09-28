import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

noncomputable section

namespace PoincareConjecture.SpectralHeatNative

open Filter
open scoped Topology

variable {iota : Type*}

abbrev State (iota : Type*) : Type _ := lp (fun _ : iota => ℝ) 2

private theorem multiplier_mem (m : iota → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hm : ∀ i, |m i| ≤ C) (x : State iota) :
    Memℓp (fun i => m i * x i) 2 := by
  apply ((lp.memℓp x).const_smul C).mono'
  intro i
  simpa only [norm_mul, Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul,
    abs_mul, abs_of_nonneg hC] using
    mul_le_mul_of_nonneg_right (hm i) (abs_nonneg (x i))

def multiplier (m : iota → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ i, |m i| ≤ C) : State iota →L[ℝ] State iota :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun i => m i * x i, multiplier_mem m hC hm x⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        exact mul_add _ _ _
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        change m i * (c * x i) = c * (m i * x i)
        ring }
    C (by
      intro x
      calc
        ‖(⟨fun i => m i * x i, multiplier_mem m hC hm x⟩ : State iota)‖
            ≤ ‖C • x‖ := by
          apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
          intro i
          simpa only [norm_mul, Real.norm_eq_abs, lp.coeFn_smul,
            Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hC] using
            mul_le_mul_of_nonneg_right (hm i) (abs_nonneg (x i))
        _ = C * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC])

@[simp] theorem multiplier_apply (m : iota → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ i, |m i| ≤ C) (x : State iota) (i : iota) :
    multiplier m C hC hm x i = m i * x i := rfl

theorem norm_multiplier_apply_le (m : iota → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ i, |m i| ≤ C) (x : State iota) :
    ‖multiplier m C hC hm x‖ ≤ C * ‖x‖ := by
  calc
    ‖multiplier m C hC hm x‖ ≤ ‖C • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro i
      simp only [multiplier_apply, norm_mul, Real.norm_eq_abs,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hm i) (abs_nonneg (x i))
    _ = C * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

private theorem heatCoefficient_bound (lambda : iota → NNReal) (t : NNReal)
    (i : iota) : |Real.exp (-(t : ℝ) * (lambda i : ℝ))| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg)
    (lambda i).coe_nonneg

def heat (lambda : iota → NNReal) (t : NNReal) :
    State iota →L[ℝ] State iota :=
  multiplier (fun i => Real.exp (-(t : ℝ) * (lambda i : ℝ))) 1
    zero_le_one (heatCoefficient_bound lambda t)

@[simp] theorem heat_apply (lambda : iota → NNReal) (t : NNReal)
    (x : State iota) (i : iota) :
    heat lambda t x i = Real.exp (-(t : ℝ) * (lambda i : ℝ)) * x i := rfl

theorem norm_heat_apply_le (lambda : iota → NNReal) (t : NNReal)
    (x : State iota) : ‖heat lambda t x‖ ≤ ‖x‖ := by
  simpa only [heat, one_mul] using norm_multiplier_apply_le _ 1 zero_le_one
    (heatCoefficient_bound lambda t) x

@[simp] theorem heat_zero (lambda : iota → NNReal) :
    heat lambda 0 = ContinuousLinearMap.id ℝ (State iota) := by
  ext x i
  simp

theorem heat_add (lambda : iota → NNReal) (s t : NNReal) :
    heat lambda (s + t) = (heat lambda s).comp (heat lambda t) := by
  ext x i
  simp only [heat_apply, NNReal.coe_add, ContinuousLinearMap.comp_apply]
  rw [show -((s : ℝ) + t) * lambda i =
    -(s : ℝ) * lambda i + -(t : ℝ) * lambda i by ring, Real.exp_add]
  ring

theorem norm_sq_eq_tsum (x : State iota) :
    ‖x‖ ^ 2 = ∑' i, |x i| ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) x

theorem continuous_heat_apply (lambda : iota → NNReal) (x : State iota) :
    Continuous (fun t : NNReal => heat lambda t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsum : Summable (fun i => |x i| ^ 2) := by
    simpa using (lp.memℓp x).summable
      (by norm_num : 0 < (2 : ENNReal).toReal)
  have hconv : Tendsto
      (fun s : NNReal => ∑' i,
        |(Real.exp (-(s : ℝ) * lambda i) -
          Real.exp (-(t : ℝ) * lambda i)) * x i| ^ 2)
      (𝓝 t) (𝓝 (∑' _i : iota, (0 : ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence hsum
    · intro i
      have hc : Continuous (fun s : NNReal =>
          |(Real.exp (-(s : ℝ) * lambda i) -
            Real.exp (-(t : ℝ) * lambda i)) * x i| ^ 2) := by
        fun_prop
      simpa using (hc.continuousAt (x := t)).tendsto
    · apply Filter.Eventually.of_forall
      intro s i
      have hs := heatCoefficient_bound lambda s i
      have ht := heatCoefficient_bound lambda t i
      have hd : |Real.exp (-(s : ℝ) * lambda i) -
          Real.exp (-(t : ℝ) * lambda i)| ≤ 1 := by
        rw [abs_le]
        rw [abs_of_pos (Real.exp_pos _)] at hs ht
        constructor <;> linarith [Real.exp_pos (-(s : ℝ) * lambda i),
          Real.exp_pos (-(t : ℝ) * lambda i)]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_mul]
      apply pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hd (abs_nonneg (x i))
  have hnorm : ∀ s : NNReal,
      ‖heat lambda s x - heat lambda t x‖ ^ 2 =
        ∑' i, |(Real.exp (-(s : ℝ) * lambda i) -
          Real.exp (-(t : ℝ) * lambda i)) * x i| ^ 2 := by
    intro s
    rw [norm_sq_eq_tsum]
    congr 1
    funext i
    simp only [lp.coeFn_sub, Pi.sub_apply, heat_apply, sub_mul]
  simp only [tsum_zero] at hconv
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hconv
  simpa only [Function.comp_def, ← hnorm, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

theorem spectralCoefficient_bound {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a) :
    |a * Real.exp (-t * a)| ≤ t⁻¹ := by
  rw [abs_of_nonneg (mul_nonneg ha (Real.exp_nonneg _)), inv_eq_one_div,
    le_div_iff₀ ht]
  have h := (Real.mul_exp_neg_le_exp_neg_one (t * a)).trans
    (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  calc
    a * Real.exp (-t * a) * t = (t * a) * Real.exp (-(t * a)) := by
      rw [neg_mul]
      ring
    _ ≤ 1 := h

def heatGenerator (lambda : iota → NNReal) (t : ℝ) (ht : 0 < t) :
    State iota →L[ℝ] State iota :=
  multiplier (fun i => (lambda i : ℝ) * Real.exp (-t * lambda i))
    t⁻¹ (inv_nonneg.mpr ht.le)
    (fun i => spectralCoefficient_bound ht (lambda i).coe_nonneg)

@[simp] theorem heatGenerator_apply (lambda : iota → NNReal) (t : ℝ)
    (ht : 0 < t) (x : State iota) (i : iota) :
    heatGenerator lambda t ht x i =
      (lambda i : ℝ) * Real.exp (-t * lambda i) * x i := rfl

theorem norm_heatGenerator_apply_le (lambda : iota → NNReal) (t : ℝ)
    (ht : 0 < t) (x : State iota) :
    ‖heatGenerator lambda t ht x‖ ≤ t⁻¹ * ‖x‖ :=
  norm_multiplier_apply_le _ _ _ _ x

theorem spectralCoefficient_pow_bound {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a)
    (k : ℕ) : |a ^ k * Real.exp (-t * a)| ≤ (k.factorial : ℝ) / t ^ k := by
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  have hpoly := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (t * a) (mul_nonneg ht.le ha) k)
  have h := mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg (-(t * a)))
  have hcancel : (Real.exp (t * a) * (k.factorial : ℝ)) *
      Real.exp (-(t * a)) = k.factorial := by
    rw [mul_right_comm, ← Real.exp_add]
    simp
  rw [hcancel] at h
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg ha k) (Real.exp_nonneg _)),
    le_div_iff₀ (pow_pos ht k)]
  calc
    a ^ k * Real.exp (-t * a) * t ^ k =
        (t * a) ^ k * Real.exp (-(t * a)) := by
      rw [neg_mul, mul_pow]
      ring
    _ ≤ k.factorial := h

def heatPower (lambda : iota → NNReal) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    State iota →L[ℝ] State iota :=
  multiplier (fun i => (lambda i : ℝ) ^ k * Real.exp (-t * lambda i))
    ((k.factorial : ℝ) / t ^ k) (by positivity)
    (fun i => spectralCoefficient_pow_bound ht (lambda i).coe_nonneg k)

@[simp] theorem heatPower_apply (lambda : iota → NNReal) (k : ℕ) (t : ℝ)
    (ht : 0 < t) (x : State iota) (i : iota) :
    heatPower lambda k t ht x i =
      (lambda i : ℝ) ^ k * Real.exp (-t * lambda i) * x i := rfl

theorem norm_heatPower_apply_le (lambda : iota → NNReal) (k : ℕ) (t : ℝ)
    (ht : 0 < t) (x : State iota) :
    ‖heatPower lambda k t ht x‖ ≤ (k.factorial : ℝ) / t ^ k * ‖x‖ :=
  norm_multiplier_apply_le _ _ _ _ x

end PoincareConjecture.SpectralHeatNative
