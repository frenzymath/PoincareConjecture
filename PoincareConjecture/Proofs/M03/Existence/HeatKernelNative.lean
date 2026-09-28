import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv










set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace PoincareConjecture

def gaussianHeatKernel (b x : ℝ) : ℝ :=
  (Real.sqrt (Real.pi / b))⁻¹ * Real.exp (-b * x ^ 2)

theorem gaussianHeatKernel_pos {b : ℝ} (hb : 0 < b) (x : ℝ) :
    0 < gaussianHeatKernel b x := by
  unfold gaussianHeatKernel
  positivity

theorem integral_gaussianHeatKernel {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, gaussianHeatKernel b x = 1 := by
  have hs : Real.sqrt (Real.pi / b) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos Real.pi_pos hb))
  unfold gaussianHeatKernel
  rw [integral_const_mul, integral_gaussian]
  exact inv_mul_cancel₀ hs

theorem gaussianHeatKernel_hasDerivAt {b x : ℝ} :
  HasDerivAt (fun y ↦ gaussianHeatKernel b y)
      ((-2 * b * x) * gaussianHeatKernel b x) x := by
  let c : ℝ := (Real.sqrt (Real.pi / b))⁻¹
  have hq : HasDerivAt (fun y : ℝ ↦ -b * y ^ 2) (-2 * b * x) x := by
    have h := (hasDerivAt_const x (-b)).mul ((hasDerivAt_id x).pow 2)
    have hf : ((fun z : ℝ => -b) * (id ^ 2)) = (fun y : ℝ => -b * y ^ 2) := by
      funext y
      simp [pow_two]
    rw [hf] at h
    apply h.congr_deriv
    simp only [id_eq, Nat.cast_ofNat, zero_mul, zero_add, Nat.add_one_sub_one,
      pow_one, mul_one]
    ring
  have hq' : HasDerivAt (fun y : ℝ ↦ -2 * b * y) (-2 * b) x := by
    have h := (hasDerivAt_const x (-2 * b)).mul (hasDerivAt_id x)
    have hf : ((fun z : ℝ => -2 * b) * id) = (fun y : ℝ => -2 * b * y) := by
      funext y
      rfl
    rw [hf] at h
    simpa using h
  have he : HasDerivAt (fun y : ℝ ↦ Real.exp (-b * y ^ 2))
      (Real.exp (-b * x ^ 2) * (-2 * b * x)) x := by
    simpa only [Function.comp_def] using hq.exp
  have hc : HasDerivAt (fun _ : ℝ ↦ c) 0 x := hasDerivAt_const x c
  have h := hc.mul he
  have hf : ((fun _ : ℝ => c) * (fun y : ℝ => Real.exp (-b * y ^ 2))) =
      (fun y : ℝ => gaussianHeatKernel b y) := by
    funext y
    rfl
  rw [hf] at h
  apply h.congr_deriv
  dsimp [gaussianHeatKernel, c]
  ring

theorem gaussianHeatKernel_firstDeriv_hasDerivAt {b x : ℝ} :
    HasDerivAt (fun y ↦ (-2 * b * y) * gaussianHeatKernel b y)
      ((4 * b ^ 2 * x ^ 2 - 2 * b) * gaussianHeatKernel b x) x := by
  have hlin : HasDerivAt (fun y : ℝ ↦ -2 * b * y) (-2 * b) x := by
    have h := (hasDerivAt_const x (-2 * b)).mul (hasDerivAt_id x)
    have hf : ((fun z : ℝ => -2 * b) * id) = (fun y : ℝ => -2 * b * y) := by
      funext y
      rfl
    rw [hf] at h
    simpa using h
  have hkernel := gaussianHeatKernel_hasDerivAt (b := b) (x := x)
  have h := hlin.mul hkernel
  have hf : ((fun y : ℝ => -2 * b * y) * (fun y => gaussianHeatKernel b y)) =
      (fun y : ℝ => (-2 * b * y) * gaussianHeatKernel b y) := by
    funext y
    rfl
  rw [hf] at h
  apply h.congr_deriv
  ring

theorem gaussianHeatKernel_hasDerivAt_param {b x : ℝ} (hb : 0 < b) :
    HasDerivAt (fun z : ℝ => gaussianHeatKernel z x)
      ((1 / (2 * b) - x ^ 2) * gaussianHeatKernel b x) b := by
  let q : ℝ → ℝ := fun z => Real.pi / z
  let s : ℝ → ℝ := fun z => Real.sqrt (q z)
  let c : ℝ → ℝ := fun z => (s z)⁻¹
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hq : HasDerivAt q (-Real.pi / b ^ 2) b := by
    dsimp [q]
    have h := (hasDerivAt_inv hb0).const_mul Real.pi
    have hf : (fun z : ℝ => Real.pi * z⁻¹) = (fun z : ℝ => Real.pi / z) := by
      funext z
      simp only [div_eq_mul_inv]
    rw [hf] at h
    apply h.congr_deriv
    simp only [div_eq_mul_inv, mul_neg, neg_mul]
  have hqb : q b ≠ 0 := by
    dsimp [q]
    exact div_ne_zero Real.pi_ne_zero hb0
  have hs : HasDerivAt s ((1 / (2 * Real.sqrt (q b))) * (-Real.pi / b ^ 2)) b := by
    dsimp [s]
    exact (Real.hasDerivAt_sqrt hqb).comp b hq
  have hs0 : s b ≠ 0 := by
    dsimp [s]
    exact ne_of_gt (Real.sqrt_pos.2 (div_pos Real.pi_pos hb))
  have hc : HasDerivAt c
      (-((1 / (2 * Real.sqrt (q b))) * (-Real.pi / b ^ 2)) / (s b) ^ 2) b := by
    exact hs.inv hs0
  have hlin : HasDerivAt (fun z : ℝ => -z * x ^ 2) (-x ^ 2) b := by
    have h := (hasDerivAt_mul_const (x ^ 2) (x := b)).neg
    have hf : (-fun z : ℝ => z * x ^ 2) = (fun z : ℝ => -z * x ^ 2) := by
      funext z
      change -(z * x ^ 2) = -z * x ^ 2
      ring
    rw [hf] at h
    simpa using h
  have he : HasDerivAt (fun z : ℝ => Real.exp (-z * x ^ 2))
      (Real.exp (-b * x ^ 2) * (-x ^ 2)) b := by
    simpa only [Function.comp_def] using hlin.exp
  have h := hc.mul he
  have hf : ((fun z : ℝ => c z) * (fun z : ℝ => Real.exp (-z * x ^ 2))) =
      (fun z : ℝ => gaussianHeatKernel z x) := by
    funext z
    rfl
  rw [hf] at h
  apply h.congr_deriv
  dsimp [c, s, q, gaussianHeatKernel] at *
  have hsquare : Real.sqrt (Real.pi / b) ^ 2 = Real.pi / b :=
    Real.sq_sqrt (le_of_lt (div_pos Real.pi_pos hb))
  rw [hsquare]
  field_simp [hb0, hs0]
  ring

def gaussianHeatKernelTime (t x : ℝ) : ℝ :=
  gaussianHeatKernel (1 / (4 * t)) x

theorem gaussianHeatKernelTime_pos {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 < gaussianHeatKernelTime t x := by
  exact gaussianHeatKernel_pos (by positivity) x

theorem integral_gaussianHeatKernelTime {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, gaussianHeatKernelTime t x = 1 := by
  exact integral_gaussianHeatKernel (by positivity)

theorem gaussianHeatKernelTime_hasDerivAt_time {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => gaussianHeatKernelTime u x)
      ((x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernelTime t x) t := by
  let bfun : ℝ → ℝ := fun u => 1 / (4 * u)
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hbfun : HasDerivAt bfun (-1 / (4 * t ^ 2)) t := by
    dsimp [bfun]
    have h := (hasDerivAt_const t (1 / 4)).mul (hasDerivAt_inv ht0)
    have hfun : ((fun z : ℝ => (1 / 4)) * (fun z : ℝ => z⁻¹)) =
        (fun z : ℝ => 1 / (4 * z)) := by
      funext z
      change (1 / 4) * z⁻¹ = 1 / (4 * z)
      field_simp
    rw [hfun] at h
    apply h.congr_deriv
    field_simp
    ring
  have hbpos : 0 < bfun t := by
    dsimp [bfun]
    positivity
  have hg := (gaussianHeatKernel_hasDerivAt_param
      (b := bfun t) (x := x) hbpos).comp t hbfun
  have hfun : (fun z : ℝ => gaussianHeatKernel z x) ∘ bfun =
      (fun u : ℝ => gaussianHeatKernelTime u x) := by
    funext u
    rfl
  rw [hfun] at hg
  apply hg.congr_deriv
  dsimp [gaussianHeatKernelTime, bfun]
  field_simp [ht0]
  ring

theorem gaussianHeatKernelTime_hasDerivAt_space {t x : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (-2 * (1 / (4 * t)) * y) * gaussianHeatKernelTime t y)
      ((4 * (1 / (4 * t)) ^ 2 * x ^ 2 - 2 * (1 / (4 * t))) *
        gaussianHeatKernelTime t x) x := by
  have hbpos : 0 < (1 / (4 * t) : ℝ) := by positivity
  have hg := gaussianHeatKernel_firstDeriv_hasDerivAt
    (b := (1 / (4 * t) : ℝ)) (x := x)
  have hfun : (fun y : ℝ => (-2 * (1 / (4 * t)) * y) *
      gaussianHeatKernel (1 / (4 * t)) y) =
      (fun y : ℝ => (-2 * (1 / (4 * t)) * y) * gaussianHeatKernelTime t y) := by
    funext y
    rfl
  rw [hfun] at hg
  apply hg.congr_deriv
  dsimp [gaussianHeatKernelTime]

theorem gaussianHeatKernelTime_heatEquation {t x : ℝ} (_ht : 0 < t) :
    (x ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gaussianHeatKernelTime t x =
      (4 * (1 / (4 * t)) ^ 2 * x ^ 2 - 2 * (1 / (4 * t))) *
        gaussianHeatKernelTime t x := by
  ring

theorem gaussianHeatKernelTime_deriv_eq_spaceSecondDeriv {t x : ℝ} (ht : 0 < t) :
    deriv (fun u : ℝ => gaussianHeatKernelTime u x) t =
      deriv (fun y : ℝ => (-2 * (1 / (4 * t)) * y) * gaussianHeatKernelTime t y) x := by
  rw [(gaussianHeatKernelTime_hasDerivAt_time ht).deriv,
    (gaussianHeatKernelTime_hasDerivAt_space ht).deriv]
  exact gaussianHeatKernelTime_heatEquation ht

end PoincareConjecture
