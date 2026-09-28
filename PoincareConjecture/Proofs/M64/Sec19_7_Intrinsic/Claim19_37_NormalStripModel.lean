import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalJacobi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture




theorem m64Intrinsic_normal_jacobi_ge_model
    {R kappa alpha : ℝ} (hR : 0 < R) (hkappa : 0 < kappa)
    {J J' J'' k : ℝ → ℝ}
    (hJ : ∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t)
    (hJ' : ContinuousOn J' (Icc (0 : ℝ) R))
    (hJ'' : ∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t)
    (hzero : J 0 = 1) (hinitial : -alpha ≤ J' 0)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) R, J'' t + k t * J t = 0)
    (hk : ∀ t ∈ Ioo (0 : ℝ) R, k t ≤ kappa ^ 2)
    (hpos : ∀ t ∈ Icc (0 : ℝ) R,
      0 < Real.cos (kappa * t) - alpha / kappa * Real.sin (kappa * t)) :
    ∀ t ∈ Icc (0 : ℝ) R,
      Real.cos (kappa * t) - alpha / kappa * Real.sin (kappa * t) ≤ J t := by
  let M : ℝ → ℝ := fun t => Real.cos (kappa * t) -
    alpha / kappa * Real.sin (kappa * t)
  let M' : ℝ → ℝ := fun t => -kappa * Real.sin (kappa * t) -
    alpha * Real.cos (kappa * t)
  let M'' : ℝ → ℝ := fun t => -kappa ^ 2 * Real.cos (kappa * t) +
    alpha * kappa * Real.sin (kappa * t)
  have hsin (t : ℝ) : HasDerivAt (fun s => Real.sin (kappa * s))
      (kappa * Real.cos (kappa * t)) t := by
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using
      (Real.hasDerivAt_sin (kappa * t)).comp t ((hasDerivAt_id t).const_mul kappa)
  have hcos (t : ℝ) : HasDerivAt (fun s => Real.cos (kappa * s))
      (-kappa * Real.sin (kappa * t)) t := by
    simpa only [Function.comp_def, id_eq, mul_one, mul_comm, neg_mul, mul_neg] using
      (Real.hasDerivAt_cos (kappa * t)).comp t ((hasDerivAt_id t).const_mul kappa)
  have hM (t : ℝ) : HasDerivAt M (M' t) t := by
    convert! (hcos t).sub ((hsin t).const_mul (alpha / kappa)) using 1
    dsimp only [M']
    field_simp
  have hM' (t : ℝ) : HasDerivAt M' (M'' t) t := by
    convert! ((hsin t).const_mul (-kappa)).sub ((hcos t).const_mul alpha) using 1
    dsimp only [M'']
    ring
  apply m64Intrinsic_jacobi_ge_positive_model (kappa := kappa) hR hJ hJ' hJ''
    (fun t _ => hM t) (by dsimp only [M']; fun_prop) (fun t _ => hM' t) hpos
  · simpa only [M, mul_zero, Real.cos_zero, Real.sin_zero, mul_zero, sub_zero] using hzero
  · simpa only [M', mul_zero, Real.sin_zero, Real.cos_zero, mul_one,
      zero_sub] using hinitial
  · exact hjac
  · intro t _
    dsimp only [M, M'']
    field_simp
    ring
  · exact hk




theorem m64Intrinsic_exists_normal_model_radius
    {delta kappa alpha : ℝ} (hdelta : 0 < delta)
    (hkappa : 0 < kappa) (halpha : 0 ≤ alpha) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∀ t ∈ Icc (0 : ℝ) R,
        1 - delta ≤ Real.cos (kappa * t) - alpha / kappa * Real.sin (kappa * t) := by
  let D := 1 + alpha + kappa ^ 2
  let R := min (1 / 20 : ℝ) (delta / (2 * D))
  have hD : 0 < D := by dsimp only [D]; positivity
  have hR : 0 < R := lt_min (by norm_num) (div_pos hdelta (mul_pos (by norm_num) hD))
  refine ⟨R, hR, (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro t ht
  have ht1 : t ≤ 1 := ht.2.trans ((min_le_left _ _).trans (by norm_num))
  have htD : t * (2 * D) ≤ delta :=
    (le_div_iff₀ (mul_pos (by norm_num) hD)).mp (ht.2.trans (min_le_right _ _))
  have hsq : t ^ 2 ≤ t := by nlinarith [ht.1]
  have hcost := Real.one_sub_sq_div_two_le_cos (x := kappa * t)
  have hsin := mul_le_mul_of_nonneg_left (Real.sin_le (mul_nonneg hkappa.le ht.1))
    (div_nonneg halpha hkappa.le)
  have hcancel : alpha / kappa * (kappa * t) = alpha * t := by field_simp
  rw [hcancel] at hsin
  have hquad : kappa ^ 2 * t ^ 2 ≤ kappa ^ 2 * t :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg kappa)
  dsimp only [D] at htD
  nlinarith [mul_nonneg halpha ht.1, mul_nonneg (sq_nonneg kappa) ht.1]




theorem m64Intrinsic_exists_uniform_normal_jacobi_radius
    {delta kappa alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hkappa : 0 < kappa) (halpha : 0 ≤ alpha) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∀ J J' J'' k : ℝ → ℝ,
        (∀ t ∈ Icc (0 : ℝ) R, HasDerivAt J (J' t) t) →
        ContinuousOn J' (Icc (0 : ℝ) R) →
        (∀ t ∈ Ioo (0 : ℝ) R, HasDerivAt J' (J'' t) t) →
        J 0 = 1 → -alpha ≤ J' 0 →
        (∀ t ∈ Ioo (0 : ℝ) R, J'' t + k t * J t = 0) →
        (∀ t ∈ Ioo (0 : ℝ) R, k t ≤ kappa ^ 2) →
        ∀ t ∈ Icc (0 : ℝ) R, 1 - delta ≤ J t := by
  obtain ⟨R, hR, hRsmall, hmodel⟩ :=
    m64Intrinsic_exists_normal_model_radius hdelta hkappa halpha
  refine ⟨R, hR, hRsmall, ?_⟩
  intro J J' J'' k hJ hJ' hJ'' hzero hinitial hjac hk
  have hcomp := m64Intrinsic_normal_jacobi_ge_model hR hkappa hJ hJ' hJ'' hzero hinitial
    hjac hk (fun t ht => (sub_pos.mpr hdelta1).trans_le (hmodel t ht))
  exact fun t ht => (hmodel t ht).trans (hcomp t ht)




theorem m64Intrinsic_exists_uniform_normal_jacobi_subinterval_radius
    {delta kappa alpha : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hkappa : 0 < kappa) (halpha : 0 ≤ alpha) :
    ∃ R : ℝ, 0 < R ∧ R < 1 / 10 ∧
      ∀ b : ℝ, 0 < b → b ≤ R → ∀ J J' J'' k : ℝ → ℝ,
        (∀ t ∈ Icc (0 : ℝ) b, HasDerivAt J (J' t) t) →
        ContinuousOn J' (Icc (0 : ℝ) b) →
        (∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt J' (J'' t) t) →
        J 0 = 1 → -alpha ≤ J' 0 →
        (∀ t ∈ Ioo (0 : ℝ) b, J'' t + k t * J t = 0) →
        (∀ t ∈ Ioo (0 : ℝ) b, k t ≤ kappa ^ 2) →
        ∀ t ∈ Icc (0 : ℝ) b, 1 - delta ≤ J t := by
  obtain ⟨R, hR, hRsmall, hmodel⟩ :=
    m64Intrinsic_exists_normal_model_radius hdelta hkappa halpha
  refine ⟨R, hR, hRsmall, ?_⟩
  intro b hb hbR J J' J'' k hJ hJ' hJ'' hzero hinitial hjac hk
  have hm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) b) := hmodel t ⟨ht.1, ht.2.trans hbR⟩
  have hcomp := m64Intrinsic_normal_jacobi_ge_model hb hkappa hJ hJ' hJ'' hzero hinitial
    hjac hk (fun t ht => (sub_pos.mpr hdelta1).trans_le (hm t ht))
  exact fun t ht => (hm t ht).trans (hcomp t ht)

end PoincareConjecture
