import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.FiniteCover
import Mathlib.Analysis.SpecificLimits.Normed









set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace Poincare.CurvatureIntegral

theorem exists_geometric_annulus_containing
    {A B r₀ q d : ℝ} (hA : 0 < A) (hB : 0 < B) (hr₀ : 0 < r₀)
    (hq : 0 < q) (hq1 : q < 1) (hgap : A < B * q)
    (hd : 0 < d) (hdB : d < B * r₀) :
    ∃ j : ℕ, A * (r₀ * q ^ j) < d ∧ d < B * (r₀ * q ^ j) := by
  by_cases hlarge : A * r₀ < d
  · exact ⟨0, by simpa only [pow_zero, mul_one] using hlarge,
      by simpa only [pow_zero, mul_one] using hdB⟩
  have hratio : A / B < q := (div_lt_iff₀ hB).mpr (by linarith only [hgap])
  have hbtwn : d / (B * r₀) < d / (A * r₀) * q := by
    calc
      d / (B * r₀) = d / (A * r₀) * (A / B) := by field_simp
      _ < _ := mul_lt_mul_of_pos_left hratio (div_pos hd (mul_pos hA hr₀))
  obtain ⟨j, hj, hj'⟩ := exists_pow_btwn_of_lt_mul hbtwn
    (div_pos hd (mul_pos hA hr₀))
    ((div_le_one (mul_pos hA hr₀)).mpr (le_of_not_gt hlarge)) hq hq1
  have hlo := (lt_div_iff₀ (mul_pos hA hr₀)).mp hj'
  have hhi := (div_lt_iff₀ (mul_pos hB hr₀)).mp hj
  exact ⟨j, by nlinarith only [hlo], by nlinarith only [hhi]⟩

theorem exists_finite_geometric_annulus_cover
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K) (p : X)
    {A B r₀ q : ℝ} (hA : 0 < A) (hB : 0 < B) (hr₀ : 0 < r₀)
    (hq : 0 < q) (hq1 : q < 1) (hgap : A < B * q)
    (hsub : K ⊆ {x | 0 < dist p x ∧ dist p x < B * r₀}) :
    ∃ F : Finset ℕ, K ⊆ ⋃ j ∈ F,
      {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)} := by
  apply hK.elim_finite_subcover
    (fun j => {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)})
  · intro j
    exact (isOpen_lt continuous_const (continuous_const.dist continuous_id)).inter
      (isOpen_lt (continuous_const.dist continuous_id) continuous_const)
  · intro x hx
    obtain ⟨j, hj⟩ := exists_geometric_annulus_containing hA hB hr₀ hq hq1 hgap
      (hsub hx).1 (hsub hx).2
    exact mem_iUnion.mpr ⟨j, hj⟩

theorem integral_le_of_geometric_annulus_bounds
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {K : Set X} (hK : IsCompact K) (p : X)
    {A B r₀ q C : ℝ} {m : ℕ} (hA : 0 < A) (hB : 0 < B) (hr₀ : 0 < r₀)
    (hq : 0 < q) (hq1 : q < 1) (hgap : A < B * q) (hC : 0 ≤ C) (hm : 1 ≤ m)
    {h : X → ℝ} (hhn : ∀ x, 0 ≤ h x) (hKi : IntegrableOn h K μ)
    (hsub : K ⊆ {x | 0 < dist p x ∧ dist p x < B * r₀})
    (hi : ∀ j : ℕ, IntegrableOn h
      {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)} μ)
    (hbound : ∀ j : ℕ,
      (∫ x in {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)},
        h x ∂μ) ≤ C * (r₀ * q ^ j) ^ m) :
    (∫ x in K, h x ∂μ) ≤ C * r₀ ^ m / (1 - q ^ m) := by
  classical
  obtain ⟨F, hcover⟩ := exists_finite_geometric_annulus_cover
    hK p hA hB hr₀ hq hq1 hgap hsub
  let U := fun j : ℕ =>
    {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)}
  have hU (j : ℕ) : MeasurableSet (U j) :=
    ((isOpen_lt continuous_const (continuous_const.dist continuous_id)).inter
      (isOpen_lt (continuous_const.dist continuous_id) continuous_const)).measurableSet
  have hcoverBound := integral_le_sum_of_finset_cover hK.isClosed.measurableSet F U
    (fun j _ => hU j) hhn hKi (fun j _ => hi j) hcover
  have hpow : |q ^ m| < 1 := by
    rw [abs_of_nonneg (pow_nonneg hq.le _)]
    exact pow_lt_one₀ hq.le hq1 (by omega)
  have hsum := (summable_geometric_of_abs_lt_one hpow).sum_le_tsum F
    (fun j _ => pow_nonneg (pow_nonneg hq.le m) j)
  rw [tsum_geometric_of_abs_lt_one hpow] at hsum
  calc
    (∫ x in K, h x ∂μ) ≤ ∑ j ∈ F, ∫ x in U j, h x ∂μ := hcoverBound
    _ ≤ ∑ j ∈ F, C * (r₀ * q ^ j) ^ m := Finset.sum_le_sum (fun j _ => hbound j)
    _ = C * r₀ ^ m * ∑ j ∈ F, (q ^ m) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow, ← pow_mul, Nat.mul_comm j m, pow_mul]
      ring
    _ ≤ C * r₀ ^ m * (1 - q ^ m)⁻¹ :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hC (pow_nonneg hr₀.le _))
    _ = C * r₀ ^ m / (1 - q ^ m) := by rw [div_eq_mul_inv]



theorem integral_le_of_geometric_annulus_bounds_above_scale
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {K : Set X} (hK : IsCompact K) (p : X)
    {A B r₀ q C s : ℝ} {m : ℕ} (hA : 0 < A) (hB : 0 < B) (hr₀ : 0 < r₀)
    (hq : 0 < q) (hq1 : q < 1) (hgap : A < B * q) (hC : 0 ≤ C) (hm : 1 ≤ m)
    (hs : 0 ≤ s) {h : X → ℝ} (hhn : ∀ x, 0 ≤ h x) (hKi : IntegrableOn h K μ)
    (hsub : K ⊆ {x | B * s < dist p x ∧ dist p x < B * r₀})
    (hi : ∀ j : ℕ, IntegrableOn h
      {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)} μ)
    (hbound : ∀ j : ℕ, s ≤ r₀ * q ^ j →
      (∫ x in {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)},
        h x ∂μ) ≤ C * (r₀ * q ^ j) ^ m) :
    (∫ x in K, h x ∂μ) ≤ C * r₀ ^ m / (1 - q ^ m) := by
  classical
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hIi : Integrable (K.indicator h) μ := (integrable_indicator_iff hKm).mpr hKi
  have hIhn (x : X) : 0 ≤ K.indicator h x := indicator_nonneg (fun y _ => hhn y) x
  have hUbound (j : ℕ) :
      (∫ x in {x | A * (r₀ * q ^ j) < dist p x ∧ dist p x < B * (r₀ * q ^ j)},
        K.indicator h x ∂μ) ≤ C * (r₀ * q ^ j) ^ m := by
    by_cases hj : s ≤ r₀ * q ^ j
    · apply (integral_mono hIi.integrableOn (hi j) ?_).trans (hbound j hj)
      intro x
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        exact hhn x
    · have hzero : ∀ x ∈ {x | A * (r₀ * q ^ j) < dist p x ∧
          dist p x < B * (r₀ * q ^ j)}, K.indicator h x = 0 := by
        intro x hx
        apply indicator_of_notMem
        intro hxK
        have hlo := (hsub hxK).1
        have hhi := hx.2
        have hmul := mul_lt_mul_of_pos_left (lt_of_not_ge hj) hB
        linarith
      have hUm : MeasurableSet {x | A * (r₀ * q ^ j) < dist p x ∧
          dist p x < B * (r₀ * q ^ j)} :=
        ((isOpen_lt continuous_const (continuous_const.dist continuous_id)).inter
          (isOpen_lt (continuous_const.dist continuous_id) continuous_const)).measurableSet
      rw [setIntegral_congr_fun hUm hzero, integral_zero]
      exact mul_nonneg hC (pow_nonneg (mul_nonneg hr₀.le (pow_nonneg hq.le _)) _)
  have hbnd := integral_le_of_geometric_annulus_bounds hK p hA hB hr₀ hq hq1 hgap
    hC hm hIhn hIi.integrableOn
    (fun x hx => ⟨(mul_nonneg hB.le hs).trans_lt (hsub hx).1, (hsub hx).2⟩)
    (fun _ => hIi.integrableOn) hUbound
  rw [setIntegral_indicator hKm] at hbnd
  simpa only [inter_self] using hbnd

end Poincare.CurvatureIntegral
