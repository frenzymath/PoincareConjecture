import PoincareConjecture.Proofs.M07.Analysis.ODE.Linear
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set intervalIntegral
open scoped Topology Interval

noncomputable section
set_option autoImplicit false

namespace Poincare.ODE.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pairCoeff (R : ℝ → E →L[ℝ] E) (t : ℝ) : (E × E) →L[ℝ] E × E :=
  (ContinuousLinearMap.snd ℝ E E).prod (-((R t).comp (ContinuousLinearMap.fst ℝ E E)))

@[simp] theorem pairCoeff_apply (R : ℝ → E →L[ℝ] E) (t : ℝ) (p : E × E) :
    pairCoeff R t p = (p.2, -(R t) p.1) := rfl

theorem norm_pairCoeff_le (R : ℝ → E →L[ℝ] E) (t : ℝ) :
    ‖pairCoeff R t‖ ≤ max 1 ‖R t‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (le_trans zero_le_one (le_max_left _ _)) fun p => ?_
  have hp : ‖pairCoeff R t p‖ = max ‖p.2‖ ‖(R t) p.1‖ := by
    simp [Prod.norm_def]
  rw [hp]
  refine max_le ?_ ?_
  · calc
      ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
      _ = 1 * ‖p‖ := (one_mul _).symm
      _ ≤ max 1 ‖R t‖ * ‖p‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · calc
      ‖(R t) p.1‖ ≤ ‖R t‖ * ‖p.1‖ := (R t).le_opNorm _
      _ ≤ ‖R t‖ * ‖p‖ := mul_le_mul_of_nonneg_left (norm_fst_le p) (norm_nonneg _)
      _ ≤ max 1 ‖R t‖ * ‖p‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

structure IsJacobiSolOn (R : ℝ → E →L[ℝ] E) (a b : ℝ) (y v : ℝ → E) : Prop where
  hasDerivWithinAt_fst : ∀ t ∈ Icc a b,
    HasDerivWithinAt y (v t) (Icc a b) t
  hasDerivWithinAt_snd : ∀ t ∈ Icc a b,
    HasDerivWithinAt v (-(R t) (y t)) (Icc a b) t

namespace IsJacobiSolOn

variable {R : ℝ → E →L[ℝ] E} {a b : ℝ} {y v : ℝ → E}

theorem continuousOn_fst (h : IsJacobiSolOn R a b y v) : ContinuousOn y (Icc a b) :=
  fun t ht => (h.hasDerivWithinAt_fst t ht).continuousWithinAt

theorem continuousOn_snd (h : IsJacobiSolOn R a b y v) : ContinuousOn v (Icc a b) :=
  fun t ht => (h.hasDerivWithinAt_snd t ht).continuousWithinAt

theorem isSolOn_pair (h : IsJacobiSolOn R a b y v) :
    Poincare.ODE.Linear.IsSolOn (pairCoeff R) a b (fun t => (y t, v t)) := by
  intro t ht
  simpa using (h.hasDerivWithinAt_fst t ht).prodMk (h.hasDerivWithinAt_snd t ht)

theorem max_norm_le {C : ℝ} (h : IsJacobiSolOn R a b y v)
    (hC : ∀ t ∈ Icc a b, ‖R t‖ ≤ C) :
    ∀ t ∈ Icc a b,
      max ‖y t‖ ‖v t‖ ≤ max ‖y a‖ ‖v a‖ * Real.exp (max 1 C * (t - a)) := by
  intro t ht
  set f : ℝ → E × E := fun s => (y s, v s)
  have hcont : ContinuousOn f (Icc a b) := h.isSolOn_pair.continuousOn
  have hderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt f (pairCoeff R x (f x)) (Ici x) x := fun x hx =>
    (h.isSolOn_pair x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Poincare.ODE.Linear.Icc_mem_nhdsWithin_Ici hx)
  have hbound : ∀ x ∈ Ico a b,
      ‖pairCoeff R x (f x)‖ ≤ max 1 C * ‖f x‖ + 0 := by
    intro x hx
    rw [add_zero]
    exact ((pairCoeff R x).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      ((norm_pairCoeff_le R x).trans
        (max_le_max le_rfl (hC x (Ico_subset_Icc_self hx)))) (norm_nonneg _))
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont hderiv
    (le_refl ‖f a‖) hbound t ht
  rw [gronwallBound_ε0] at hg
  simpa [f, Prod.norm_def] using hg

end IsJacobiSolOn

variable [CompleteSpace E]

theorem sub_eq_integral_of_hasDerivWithinAt_Icc {a b : ℝ} {f f' : ℝ → E}
    (hf : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t)
    (hf' : ContinuousOn f' (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) :
    f t - f a = ∫ s in a..t, f' s := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn f (Icc a t) :=
    fun s hs => ((hf s (hsub hs)).continuousWithinAt).mono hsub
  have hderiv : ∀ x ∈ Ioo a t, HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    have hx' : x ∈ Ico a b := ⟨hx.1.le, lt_of_lt_of_le hx.2 ht.2⟩
    exact ((hf x (Ico_subset_Icc_self hx')).mono_of_mem_nhdsWithin
      (Poincare.ODE.Linear.Icc_mem_nhdsWithin_Ici hx')).mono Ioi_subset_Ici_self
  have hint : IntervalIntegrable f' MeasureTheory.volume a t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hf'.mono hsub
  exact (integral_eq_sub_of_hasDeriv_right_of_le ht.1 hcont hderiv hint).symm

namespace IsJacobiSolOn

variable {R : ℝ → E →L[ℝ] E} {b C : ℝ} {y v : ℝ → E}

omit [CompleteSpace E] in

theorem norm_snd_le (h : IsJacobiSolOn R 0 b y v)
    (hC : ∀ t ∈ Icc 0 b, ‖R t‖ ≤ C) (hy0 : y 0 = 0) :
    ∀ t ∈ Icc 0 b, ‖v t‖ ≤ ‖v 0‖ * Real.exp (max 1 C * b) := by
  intro t ht
  have hK0 : (0 : ℝ) ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have h1 := h.max_norm_le hC t ht
  rw [hy0] at h1
  rw [show max ‖(0 : E)‖ ‖v 0‖ = ‖v 0‖ by simp, sub_zero] at h1
  calc
    ‖v t‖ ≤ max ‖y t‖ ‖v t‖ := le_max_right _ _
    _ ≤ ‖v 0‖ * Real.exp (max 1 C * t) := by simpa using h1
    _ ≤ ‖v 0‖ * Real.exp (max 1 C * b) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
      exact mul_le_mul_of_nonneg_left ht.2 hK0

theorem norm_fst_le (h : IsJacobiSolOn R 0 b y v)
    (hC : ∀ t ∈ Icc 0 b, ‖R t‖ ≤ C) (hy0 : y 0 = 0) :
    ∀ t ∈ Icc 0 b, ‖y t‖ ≤ (‖v 0‖ * Real.exp (max 1 C * b)) * t := by
  intro t ht
  have key := sub_eq_integral_of_hasDerivWithinAt_Icc h.hasDerivWithinAt_fst
    h.continuousOn_snd ht
  rw [hy0, sub_zero] at key
  rw [key]
  have hbound : ∀ x ∈ Ι (0 : ℝ) t,
      ‖v x‖ ≤ ‖v 0‖ * Real.exp (max 1 C * b) := by
    intro x hx
    rw [uIoc_of_le ht.1] at hx
    exact h.norm_snd_le hC hy0 x ⟨hx.1.le, hx.2.trans ht.2⟩
  have hi := norm_integral_le_of_norm_le_const hbound
  rwa [sub_zero, abs_of_nonneg ht.1] at hi

theorem norm_snd_sub_le (h : IsJacobiSolOn R 0 b y v)
    (hR : ContinuousOn R (Icc 0 b)) (hC : ∀ t ∈ Icc 0 b, ‖R t‖ ≤ C)
    (hy0 : y 0 = 0) :
    ∀ t ∈ Icc 0 b, ‖v t - v 0‖ ≤
      C * (‖v 0‖ * Real.exp (max 1 C * b)) * t ^ 2 / 2 := by
  intro t ht
  have hC0 : (0 : ℝ) ≤ C := (norm_nonneg (R 0)).trans (hC 0 ⟨le_rfl, ht.1.trans ht.2⟩)
  set M : ℝ := ‖v 0‖ * Real.exp (max 1 C * b)
  have hRy : ContinuousOn (fun s => -(R s) (y s)) (Icc 0 b) :=
    (hR.clm_apply h.continuousOn_fst).neg
  have key := sub_eq_integral_of_hasDerivWithinAt_Icc h.hasDerivWithinAt_snd hRy ht
  rw [key]
  have hsub : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
  have hi1 : IntervalIntegrable (fun s => ‖-(R s) (y s)‖)
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact (hRy.mono hsub).norm
  have hi2 : IntervalIntegrable (fun s => C * M * s) MeasureTheory.volume 0 t :=
    intervalIntegrable_id.const_mul _
  calc
    ‖∫ s in (0 : ℝ)..t, -(R s) (y s)‖ ≤
        ∫ s in (0 : ℝ)..t, ‖-(R s) (y s)‖ := norm_integral_le_integral_norm ht.1
    _ ≤ ∫ s in (0 : ℝ)..t, C * M * s := by
      apply integral_mono_on ht.1 hi1 hi2
      intro s hs
      have hs' := hsub hs
      rw [norm_neg]
      calc
        ‖(R s) (y s)‖ ≤ ‖R s‖ * ‖y s‖ := (R s).le_opNorm _
        _ ≤ C * (M * s) := mul_le_mul (hC s hs') (h.norm_fst_le hC hy0 s hs')
            (norm_nonneg _) hC0
        _ = C * M * s := by ring
    _ = C * M * t ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring

theorem norm_fst_sub_le (h : IsJacobiSolOn R 0 b y v)
    (hR : ContinuousOn R (Icc 0 b)) (hC : ∀ t ∈ Icc 0 b, ‖R t‖ ≤ C)
    (hy0 : y 0 = 0) :
    ∀ t ∈ Icc 0 b, ‖y t - t • v 0‖ ≤
      C * (‖v 0‖ * Real.exp (max 1 C * b)) * t ^ 3 / 6 := by
  intro t ht
  set M : ℝ := ‖v 0‖ * Real.exp (max 1 C * b)
  have hz : ∀ s ∈ Icc (0 : ℝ) b,
      HasDerivWithinAt (fun τ => y τ - τ • v 0) (v s - v 0) (Icc 0 b) s := by
    intro s hs
    have hsm : HasDerivWithinAt (fun τ : ℝ => τ • v 0) (v 0) (Icc 0 b) s := by
      simpa using ((hasDerivAt_id s).smul_const (v 0)).hasDerivWithinAt
    exact (h.hasDerivWithinAt_fst s hs).sub hsm
  have hcont : ContinuousOn (fun s => v s - v 0) (Icc 0 b) :=
    h.continuousOn_snd.sub continuousOn_const
  have key := sub_eq_integral_of_hasDerivWithinAt_Icc hz hcont ht
  rw [hy0] at key
  simp only [zero_smul, sub_zero] at key
  rw [key]
  have hsub : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
  have hi1 : IntervalIntegrable (fun s => ‖v s - v 0‖)
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact (hcont.mono hsub).norm
  have hi2 : IntervalIntegrable (fun s => C * M * s ^ 2 / 2)
      MeasureTheory.volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    exact Continuous.continuousOn (by fun_prop)
  calc
    ‖∫ s in (0 : ℝ)..t, (v s - v 0)‖ ≤
        ∫ s in (0 : ℝ)..t, ‖v s - v 0‖ := norm_integral_le_integral_norm ht.1
    _ ≤ ∫ s in (0 : ℝ)..t, C * M * s ^ 2 / 2 := by
      apply integral_mono_on ht.1 hi1 hi2
      intro s hs
      exact h.norm_snd_sub_le hR hC hy0 s (hsub hs)
    _ = C * M * t ^ 3 / 6 := by
      simp_rw [show ∀ s : ℝ, C * M * s ^ 2 / 2 = (C * M / 2) * s ^ 2 by intro s; ring]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring

end IsJacobiSolOn

end Poincare.ODE.Jacobi
