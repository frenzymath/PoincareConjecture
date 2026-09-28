import PoincareConjecture.Proofs.M07.Analysis.ODE.Jacobi.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace Poincare.ODE.Jacobi

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def indexIntegrand (R : ℝ → F →L[ℝ] F) (y v z w : ℝ → F) (t : ℝ) : ℝ :=
  ⟪v t, w t⟫ - ⟪R t (y t), z t⟫

def indexForm (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F) : ℝ :=
  ∫ t in a..b, indexIntegrand R y v z w t

theorem indexForm_def (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F) :
    indexForm R a b y v z w = ∫ t in a..b, indexIntegrand R y v z w t := rfl

theorem indexIntegrand_symm {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (y v z w : ℝ → F) (t : ℝ) :
    indexIntegrand R y v z w t = indexIntegrand R z w y v t := by
  unfold indexIntegrand
  rw [real_inner_comm (v t) (w t), hR t (y t) (z t),
    real_inner_comm (y t) (R t (z t))]

theorem indexForm_symm {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (a b : ℝ) (y v z w : ℝ → F) :
    indexForm R a b y v z w = indexForm R a b z w y v :=
  intervalIntegral.integral_congr fun t _ => indexIntegrand_symm hR y v z w t

theorem contOn_indexIntegrand {R : ℝ → F →L[ℝ] F} {y v z w : ℝ → F} {s : Set ℝ}
    (hR : ContinuousOn R s) (hy : ContinuousOn y s) (hv : ContinuousOn v s)
    (hz : ContinuousOn z s) (hw : ContinuousOn w s) :
    ContinuousOn (indexIntegrand R y v z w) s :=
  (hv.inner hw).sub ((hR.clm_apply hy).inner hz)

theorem intInt_indexIntegrand {R : ℝ → F →L[ℝ] F} {y v z w : ℝ → F} {a b : ℝ}
    (hR : ContinuousOn R (uIcc a b)) (hy : ContinuousOn y (uIcc a b))
    (hv : ContinuousOn v (uIcc a b)) (hz : ContinuousOn z (uIcc a b))
    (hw : ContinuousOn w (uIcc a b)) :
    IntervalIntegrable (indexIntegrand R y v z w) volume a b :=
  (contOn_indexIntegrand hR hy hv hz hw).intervalIntegrable

theorem IsJacobiSolOn.hasDerivAt_inner {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v z w : ℝ → F}
    (hy : IsJacobiSolOn R a b y v)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => (⟪v s, z s⟫ : ℝ)) (indexIntegrand R y v z w t) t := by
  have hmem : Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hv : HasDerivAt v (-(R t) (y t)) t :=
    (hy.hasDerivWithinAt_snd t (Ioo_subset_Icc_self ht)).hasDerivAt hmem
  have hzt : HasDerivAt z (w t) t :=
    (hz t (Ioo_subset_Icc_self ht)).hasDerivAt hmem
  have h := hv.inner ℝ hzt
  have hcalc : (⟪v t, w t⟫ : ℝ) + ⟪-(R t) (y t), z t⟫
      = indexIntegrand R y v z w t := by
    unfold indexIntegrand
    rw [inner_neg_left]
    ring
  rw [← hcalc]
  exact h

theorem IsJacobiSolOn.indexForm_eq_sub {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v z w : ℝ → F}
    (hab : a ≤ b) (hR : ContinuousOn R (Icc a b))
    (hy : IsJacobiSolOn R a b y v)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    (hw : ContinuousOn w (Icc a b)) :
    indexForm R a b y v z w = ⟪v b, z b⟫ - ⟪v a, z a⟫ := by
  have hzc : ContinuousOn z (Icc a b) := fun t ht => (hz t ht).continuousWithinAt
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hint : IntervalIntegrable (indexIntegrand R y v z w) volume a b := by
    refine intInt_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;> rw [huIcc]
    exacts [hR, hy.continuousOn_fst, hy.continuousOn_snd, hzc, hw]
  have hcont : ContinuousOn (fun s => (⟪v s, z s⟫ : ℝ)) (Icc a b) :=
    hy.continuousOn_snd.inner hzc
  have hderiv : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun s => (⟪v s, z s⟫ : ℝ))
        (indexIntegrand R y v z w t) (Ioi t) t :=
    fun t ht => (hy.hasDerivAt_inner hz ht).hasDerivWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont
    hderiv hint

theorem IsJacobiSolOn.indexForm_self_zero {R : ℝ → F →L[ℝ] F} {a b : ℝ}
    {y v : ℝ → F}
    (hab : a ≤ b) (hR : ContinuousOn R (Icc a b))
    (hy : IsJacobiSolOn R a b y v) (hya : y a = 0) (hyb : y b = 0) :
    indexForm R a b y v y v = 0 := by
  rw [hy.indexForm_eq_sub hab hR hy.hasDerivWithinAt_fst hy.continuousOn_snd, hya, hyb]
  simp

theorem indexForm_add_adjacent {R : ℝ → F →L[ℝ] F} {a c b : ℝ}
    {y v z w : ℝ → F}
    (h₁ : IntervalIntegrable (indexIntegrand R y v z w) volume a c)
    (h₂ : IntervalIntegrable (indexIntegrand R y v z w) volume c b) :
    indexForm R a c y v z w + indexForm R c b y v z w
      = indexForm R a b y v z w :=
  intervalIntegral.integral_add_adjacent_intervals h₁ h₂

@[simp] theorem indexForm_same (R : ℝ → F →L[ℝ] F) (a : ℝ) (y v z w : ℝ → F) :
    indexForm R a a y v z w = 0 := intervalIntegral.integral_same

theorem indexIntegrand_add_smul {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (y v z w : ℝ → F) (c : ℝ) (t : ℝ) :
    indexIntegrand R (y + c • z) (v + c • w) (y + c • z) (v + c • w) t
      = indexIntegrand R y v y v t + 2 * c * indexIntegrand R y v z w t
        + c ^ 2 * indexIntegrand R z w z w t := by
  have hcross : (⟪R t (z t), y t⟫ : ℝ) = ⟪R t (y t), z t⟫ := by
    rw [hR t (z t) (y t), real_inner_comm (z t) (R t (y t))]
  simp only [indexIntegrand, Pi.add_apply, Pi.smul_apply, map_add, map_smul,
    inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm (w t) (v t), hcross]
  ring

theorem indexForm_add_smul {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hyy : IntervalIntegrable (indexIntegrand R y v y v) volume a b)
    (hyz : IntervalIntegrable (indexIntegrand R y v z w) volume a b)
    (hzz : IntervalIntegrable (indexIntegrand R z w z w) volume a b)
    (c : ℝ) :
    indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w)
      = indexForm R a b y v y v + 2 * c * indexForm R a b y v z w
        + c ^ 2 * indexForm R a b z w z w := by
  unfold indexForm
  rw [intervalIntegral.integral_congr
    (g := fun t => indexIntegrand R y v y v t
      + 2 * c * indexIntegrand R y v z w t
      + c ^ 2 * indexIntegrand R z w z w t)
    (fun t _ => indexIntegrand_add_smul hR y v z w c t)]
  rw [intervalIntegral.integral_add
      (hyy.add (hyz.const_mul (2 * c))) (hzz.const_mul (c ^ 2)),
    intervalIntegral.integral_add hyy (hyz.const_mul (2 * c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem exists_indexForm_neg {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hyy : IntervalIntegrable (indexIntegrand R y v y v) volume a b)
    (hyz : IntervalIntegrable (indexIntegrand R y v z w) volume a b)
    (hzz : IntervalIntegrable (indexIntegrand R z w z w) volume a b)
    (hself : indexForm R a b y v y v = 0)
    (hcross : indexForm R a b y v z w ≠ 0) :
    ∃ c : ℝ,
      indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w) < 0 := by
  set κ := indexForm R a b y v z w with hκ
  set Q := indexForm R a b z w z w with hQ
  have hpos : (0 : ℝ) < |Q| + 1 := by positivity
  refine ⟨-κ / (|Q| + 1), ?_⟩
  rw [indexForm_add_smul hR hyy hyz hzz, hself, ← hκ, ← hQ]
  set c : ℝ := -κ / (|Q| + 1) with hc
  have hq : 0 + 2 * c * κ + c ^ 2 * Q = c * (2 * κ + c * Q) := by ring
  rw [hq]
  have hκpos : 0 < |κ| := abs_pos.mpr hcross
  have hcQ : |c * Q| < |κ| := by
    rw [hc, abs_mul, abs_div, abs_neg, abs_of_pos hpos,
      div_mul_eq_mul_div, div_lt_iff₀ hpos]
    nlinarith [abs_nonneg Q]
  rcases lt_or_gt_of_ne hcross with hneg | hpos'
  · have hcpos : 0 < c := by
      rw [hc]
      exact div_pos (neg_pos.mpr hneg) hpos
    have hsum : 2 * κ + c * Q < 0 := by
      have h2 := (abs_lt.mp hcQ).2
      rw [abs_of_neg hneg] at h2
      linarith
    exact mul_neg_of_pos_of_neg hcpos hsum
  · have hcneg : c < 0 := by
      rw [hc]
      refine div_neg_of_neg_of_pos ?_ hpos
      linarith
    have hsum : 0 < 2 * κ + c * Q := by
      have h1 := (abs_lt.mp hcQ).1
      rw [abs_of_pos hpos'] at h1
      linarith
    exact mul_neg_of_neg_of_pos hcneg hsum

end InnerProduct

end Poincare.ODE.Jacobi
