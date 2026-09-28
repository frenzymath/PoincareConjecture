import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.ScalarComparison
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture.RiemannianMetric

theorem radial_logarithmic_derivative_le_of_cross
    {m : ℕ} (hm : 0 < m) {κ b t : ℝ} (hκ : 0 ≤ κ)
    (ht : t ∈ Ioo 0 b) {ρ : ℝ → ℝ} (hρ : DifferentiableAt ℝ ρ t)
    (hρpos : 0 < ρ t)
    (hcross : ∀ u ∈ Ioo 0 b, ∀ v ∈ Ioo 0 b, u ≤ v →
      (v ^ m * ρ v) * modelS κ u ^ m ≤ (u ^ m * ρ u) * modelS κ v ^ m) :
    (m : ℝ) / t + deriv ρ t / ρ t ≤
      (m : ℝ) * Real.cosh (Real.sqrt κ * t) / modelS κ t := by
  let F : ℝ → ℝ := fun s => s ^ m * ρ s
  let G : ℝ → ℝ := fun s => modelS κ s ^ m
  let A : ℝ := (m : ℝ) / t + deriv ρ t / ρ t
  let B : ℝ := (m : ℝ) * Real.cosh (Real.sqrt κ * t) / modelS κ t
  have ht0 : t ≠ 0 := ht.1.ne'
  have hSpos := modelS_pos hκ ht.1
  have htpow : t ^ m = t ^ (m - 1) * t := by
    conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ]
  have hSpow : modelS κ t ^ m = modelS κ t ^ (m - 1) * modelS κ t := by
    conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ]
  have hF : HasDerivAt F (A * F t) t := by
    convert! (hasDerivAt_pow m t).mul hρ.hasDerivAt using 1
    dsimp [A, F]
    field_simp [ht0, hρpos.ne']
    rw [htpow]
    ring
  have hG : HasDerivAt G (B * G t) t := by
    convert! (hasDerivAt_modelS hκ t).pow m using 1
    dsimp [B, G]
    field_simp [hSpos.ne']
    rw [hSpow]
    ring
  have hGpos : 0 < G t := pow_pos hSpos _
  have hFpos : 0 < F t := mul_pos (pow_pos ht.1 _) hρpos
  have hq : HasDerivAt (fun s => F s / G s)
      ((F t / G t) * (A - B)) t := by
    convert! hF.div hG hGpos.ne' using 1
    field_simp
  have hanti : AntitoneOn (fun s => F s / G s) (Ioo 0 b) := by
    intro u hu v hv huv
    exact (div_le_div_iff₀ (pow_pos (modelS_pos hκ hv.1) _)
      (pow_pos (modelS_pos hκ hu.1) _)).mpr (hcross u hu v hv huv)
  have hd := hanti.derivWithin_nonpos (x := t)
  rw [derivWithin_of_isOpen isOpen_Ioo ht, hq.deriv] at hd
  exact sub_nonpos.mp ((mul_nonpos_iff_pos_imp_nonpos.mp hd).1 (div_pos hFpos hGpos))

theorem model_logarithmic_derivative_le {k t : ℝ} (hk : 0 ≤ k) (ht : 0 < t) :
    Real.cosh (Real.sqrt (k ^ 2) * t) / modelS (k ^ 2) t ≤ 1 / t + k := by
  rw [Real.sqrt_sq hk]
  by_cases hk0 : k = 0
  · subst k
    simp
  have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
  have hsinh : 0 < Real.sinh (k * t) := Real.sinh_pos_iff.mpr (mul_pos hkpos ht)
  have hexp : Real.exp (-(k * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hk ht.le)
  have hx := Real.self_le_sinh_iff.mpr (mul_nonneg hk ht.le)
  have haux : k * t * Real.cosh (k * t) ≤
      Real.sinh (k * t) + k * t * Real.sinh (k * t) := by
    have h := mul_le_mul_of_nonneg_left hexp (mul_nonneg hk ht.le)
    rw [← Real.cosh_sub_sinh] at h
    nlinarith
  rw [modelS, if_neg (pow_ne_zero 2 hk0), Real.sqrt_sq hk]
  apply (div_le_iff₀ (div_pos hsinh hkpos)).mpr
  apply (mul_le_mul_iff_right₀ hkpos).mp
  apply (mul_le_mul_iff_right₀ ht).mp
  calc
    t * (k * Real.cosh (k * t)) = k * t * Real.cosh (k * t) := by ring
    _ ≤ Real.sinh (k * t) + k * t * Real.sinh (k * t) := haux
    _ = t * (k * ((1 / t + k) * (Real.sinh (k * t) / k))) := by
      field_simp

end PoincareConjecture.RiemannianMetric
