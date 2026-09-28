import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Holder
import Mathlib.Analysis.Calculus.MeanValue










noncomputable section
set_option autoImplicit false

open Set
open scoped ContDiff NNReal ENNReal

namespace Poincare.Parabolic.Interior

section Compact

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem memHolder_half_of_contDiff_compact {f : E → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : MemHolder (1 / 2) f := by
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous hf.continuous
  obtain ⟨L, hL⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf.fderiv_right (m := ∞) (by simp)).continuous
  let M' : ℝ≥0 := ⟨max 0 M, le_max_left _ _⟩
  let L' : ℝ≥0 := ⟨max 0 L, le_max_left _ _⟩
  have hnorm (x : E) : ‖f x‖ ≤ M' := (hM x).trans (le_max_right _ _)
  have hlip : LipschitzWith L' f :=
    lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) (fun x => by
      rw [← NNReal.coe_le_coe]
      exact (hL x).trans (le_max_right _ _))
  exact ((holderWith_zero_of_norm_le hnorm).of_le_of_le hlip.holderWith
    (show (0 : ℝ≥0) ≤ 1 / 2 by positivity) (show (1 / 2 : ℝ≥0) ≤ 1 by norm_num)).memHolder



theorem memHolder_half_fderiv_of_contDiff_compact {f : E → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    MemHolder (1 / 2) (fderiv ℝ f) :=
  memHolder_half_of_contDiff_compact (hf.fderiv_right (by simp)) (hc.fderiv ℝ)

end Compact

section Product

variable {X E F : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem holderWith_clm_apply {A : X → E →L[ℝ] F} {f : X → E}
    {α HA Hf MA Mf : ℝ≥0} (hA : HolderWith HA α A) (hf : HolderWith Hf α f)
    (hAbound : ∀ x, ‖A x‖ ≤ MA) (hfbound : ∀ x, ‖f x‖ ≤ Mf) :
    HolderWith (MA * Hf + HA * Mf) α (fun x => A x (f x)) := by
  intro x y
  have hAdiff : ‖A x - A y‖ ≤ (HA : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hA.dist_le x y
  have hfdiff : ‖f x - f y‖ ≤ (Hf : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hf.dist_le x y
  have hnorm : ‖A x (f x) - A y (f y)‖ ≤
      ((MA : ℝ) * (Hf : ℝ) + (HA : ℝ) * (Mf : ℝ)) * dist x y ^ (α : ℝ) := by
    have heq : A x (f x) - A y (f y) = A x (f x - f y) + (A x - A y) (f y) := by
      simp only [map_sub, sub_apply]
      abel
    calc
      _ ≤ ‖A x (f x - f y)‖ + ‖(A x - A y) (f y)‖ := by
        rw [heq]
        exact norm_add_le _ _
      _ ≤ ‖A x‖ * ‖f x - f y‖ + ‖A x - A y‖ * ‖f y‖ :=
        add_le_add ((A x).le_opNorm _) ((A x - A y).le_opNorm _)
      _ ≤ (MA : ℝ) * ((Hf : ℝ) * dist x y ^ (α : ℝ)) +
          ((HA : ℝ) * dist x y ^ (α : ℝ)) * (Mf : ℝ) :=
        add_le_add
          (mul_le_mul (hAbound x) hfdiff (norm_nonneg _) MA.coe_nonneg)
          (mul_le_mul hAdiff (hfbound y) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  rw [edist_nndist, edist_nndist,
    ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simpa only [coe_nndist, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_rpow,
    dist_eq_norm] using hnorm


theorem nnHolderNorm_clm_apply_le {A : X → E →L[ℝ] F} {f : X → E}
    {α MA Mf : ℝ≥0} (hA : MemHolder α A) (hf : MemHolder α f)
    (hAbound : ∀ x, ‖A x‖ ≤ MA) (hfbound : ∀ x, ‖f x‖ ≤ Mf) :
    nnHolderNorm α (fun x => A x (f x)) ≤
      MA * nnHolderNorm α f + nnHolderNorm α A * Mf :=
  (holderWith_clm_apply hA.holderWith hf.holderWith hAbound hfbound).nnholderNorm_le

end Product

section Absorption

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]



theorem holderWith_of_self_improving_bound {f : X → Y} {α a b : ℝ≥0}
    (hf : MemHolder α f) (ha : a < 1)
    (hstep : ∀ H : ℝ≥0, HolderWith H α f → HolderWith (a * H + b) α f) :
    HolderWith (b / (1 - a)) α f := by
  have hnorm : nnHolderNorm α f ≤ a * nnHolderNorm α f + b :=
    (hstep _ hf.holderWith).nnholderNorm_le
  apply hf.holderWith.mono
  rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_sub ha.le, NNReal.coe_one]
  have ha' : (a : ℝ) < 1 := by exact_mod_cast ha
  rw [le_div_iff₀ (show (0 : ℝ) < 1 - a by linarith)]
  have hn : (nnHolderNorm α f : ℝ) ≤ (a : ℝ) * nnHolderNorm α f + (b : ℝ) := by
    exact_mod_cast hnorm
  nlinarith only [hn]

end Absorption

section CompactAbsorption

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem holderWith_half_fderiv_of_self_improving {f : E → F}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) {a b : ℝ≥0} (ha : a < 1)
    (hstep : ∀ H : ℝ≥0, HolderWith H (1 / 2) (fderiv ℝ f) →
      HolderWith (a * H + b) (1 / 2) (fderiv ℝ f)) :
    HolderWith (b / (1 - a)) (1 / 2) (fderiv ℝ f) :=
  holderWith_of_self_improving_bound (memHolder_half_fderiv_of_contDiff_compact hf hc) ha hstep

end CompactAbsorption

end Poincare.Parabolic.Interior
