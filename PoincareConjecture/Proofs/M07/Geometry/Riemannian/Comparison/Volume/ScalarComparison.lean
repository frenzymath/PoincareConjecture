import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Model

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace PoincareConjecture.RiemannianMetric

theorem hasDerivAt_modelS {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) :
    HasDerivAt (modelS κ) (Real.cosh (Real.sqrt κ * t)) t := by
  by_cases hκ0 : κ = 0
  · subst κ
    change HasDerivAt (fun s => modelS 0 s) _ t
    simpa [modelS] using! hasDerivAt_id t
  · have hsqrt : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hκ0))).ne'
    change HasDerivAt (fun s => modelS κ s) _ t
    simpa [modelS, hκ0, hsqrt] using
      (((hasDerivAt_id t).const_mul (Real.sqrt κ)).sinh).div_const (Real.sqrt κ)

theorem hasDerivAt_modelS_derivative {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) :
    HasDerivAt (fun s => Real.cosh (Real.sqrt κ * s)) (κ * modelS κ t) t := by
  by_cases hκ0 : κ = 0
  · subst κ
    simpa only [Real.sqrt_zero, zero_mul, Real.cosh_zero] using hasDerivAt_const t (1 : ℝ)
  · have hsqrt : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hκ (Ne.symm hκ0))).ne'
    have heq : κ * modelS κ t = Real.sinh (Real.sqrt κ * t) * Real.sqrt κ := by
      simp only [modelS, if_neg hκ0]
      rw [← mul_div_assoc]
      apply (div_eq_iff hsqrt).2
      nlinarith only [congrArg (fun z : ℝ => z * Real.sinh (Real.sqrt κ * t))
        (Real.sq_sqrt hκ)]
    simpa only [id_eq, mul_one, heq] using
      (((hasDerivAt_id t).const_mul (Real.sqrt κ)).cosh)

theorem antitoneOn_div_modelS_of_second_derivative_le
    {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R) {y y' y'' : ℝ → ℝ}
    (hy : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt y (y' t) t)
    (hy' : ContinuousOn y' (Icc (0 : ℝ) R))
    (hy'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt y' (y'' t) t)
    (hy0 : y 0 = 0)
    (hle : ∀ t ∈ Ioo (0 : ℝ) R, y'' t ≤ κ * y t) :
    AntitoneOn (fun t => y t / modelS κ t) (Ioo (0 : ℝ) R) := by
  let W : ℝ → ℝ := fun t => y' t * modelS κ t - y t * Real.cosh (Real.sqrt κ * t)
  have hyc : ContinuousOn y (Icc (0 : ℝ) R) :=
    fun t ht => (hy t ht).continuousAt.continuousWithinAt
  have hWc : ContinuousOn W (Icc (0 : ℝ) R) :=
    (hy'.mul (continuous_modelS κ).continuousOn).sub
      (hyc.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).continuousOn)
  have hWd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) :
      HasDerivAt W ((y'' t - κ * y t) * modelS κ t) t := by
    convert! ((hy'' t ht).mul (hasDerivAt_modelS hκ t)).sub
      ((hy t ⟨ht.1.le, ht.2.le⟩).mul (hasDerivAt_modelS_derivative hκ t)) using 1
    ring
  have hWa : AntitoneOn W (Icc (0 : ℝ) R) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hWc
      (fun t ht => (hWd t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) R := by simpa only [interior_Icc] using ht
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hle t ht'))
      (modelS_nonneg hκ ht'.1.le)
  have hWle (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) : W t ≤ 0 := by
    simpa only [W, modelS_zero, hy0, mul_zero, zero_mul, sub_zero] using
      hWa ⟨le_rfl, hR.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1.le
  have hquot (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) R) :
      HasDerivAt (fun t => y t / modelS κ t) (W t / modelS κ t ^ 2) t :=
    (hy t ⟨ht.1.le, ht.2.le⟩).div (hasDerivAt_modelS hκ t) (modelS_pos hκ ht.1).ne'
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo _ _)
    (fun t ht => (hquot t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hquot t (by simpa only [interior_Ioo] using ht)).hasDerivWithinAt)
  intro t ht
  exact div_nonpos_of_nonpos_of_nonneg
    (hWle t (by simpa only [interior_Ioo] using ht)) (sq_nonneg _)

end PoincareConjecture.RiemannianMetric
