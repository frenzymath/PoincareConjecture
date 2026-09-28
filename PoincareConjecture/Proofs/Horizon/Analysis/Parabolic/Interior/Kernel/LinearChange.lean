import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.Cancellation
import Mathlib.Analysis.Normed.Operator.NNNorm











noncomputable section

open MeasureTheory Real
open scoped NNReal ENNReal RealInnerProductSpace

namespace Poincare.Parabolic.Interior.Kernel

section LinearPull

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def linPull (L : V ≃L[ℝ] V) (f : V → F) : V → F :=
  f ∘ L

def linHalfConst (L : V ≃L[ℝ] V) (K : ℝ≥0) : ℝ≥0 :=
  K * ‖(L : V →L[ℝ] V)‖₊ ^ (1 / 2 : ℝ)

omit [FiniteDimensional ℝ V]
  [MeasurableSpace V]
  [BorelSpace V]
  [Nontrivial V]
  [NormedSpace ℝ F]
  [CompleteSpace F] in
theorem linPull_holder (L : V ≃L[ℝ] V) {K : ℝ≥0} {f : V → F}
    (hf : HolderWith K (1 / 2 : ℝ≥0) f) :
    HolderWith (linHalfConst L K) (1 / 2 : ℝ≥0) (linPull L f) := by
  have hL : HolderWith ‖(L : V →L[ℝ] V)‖₊ 1 L :=
    L.lipschitz.holderWith
  simpa [linPull, linHalfConst] using hf.comp hL

def linD2Cancel (L : V ≃L[ℝ] V) (t : ℝ) (v w : V)
    (f : V → F) (x : V) : F :=
  heatD2Cancel t (L.symm v) (L.symm w) (linPull L f) (L.symm x)

omit [CompleteSpace F] in
theorem linD2Cancel_norm (L : V ≃L[ℝ] V) {t : ℝ} (ht : 0 < t)
    {K : ℝ≥0} {f : V → F} (hf : HolderWith K (1 / 2 : ℝ≥0) f)
    (v w x : V) :
    ‖linD2Cancel L t v w f x‖ ≤
      ‖L.symm v‖ * ‖L.symm w‖ * (linHalfConst L K : ℝ) *
        heatScale34 t * heatC2Half V := by
  unfold linD2Cancel
  exact heatD2Cancel_norm ht (linPull_holder L hf) (L.symm v) (L.symm w) (L.symm x)

omit [CompleteSpace F] in
theorem linD2Cancel_op (L : V ≃L[ℝ] V) {t : ℝ} (ht : 0 < t)
    {K : ℝ≥0} {f : V → F} (hf : HolderWith K (1 / 2 : ℝ≥0) f)
    (v w x : V) :
    ‖linD2Cancel L t v w f x‖ ≤
      (‖(L.symm : V →L[ℝ] V)‖ * ‖v‖) *
        (‖(L.symm : V →L[ℝ] V)‖ * ‖w‖) *
        (linHalfConst L K : ℝ) * heatScale34 t * heatC2Half V := by
  refine (linD2Cancel_norm L ht hf v w x).trans ?_
  have hv : ‖L.symm v‖ ≤ ‖(L.symm : V →L[ℝ] V)‖ * ‖v‖ :=
    (L.symm : V →L[ℝ] V).le_opNorm v
  have hw : ‖L.symm w‖ ≤ ‖(L.symm : V →L[ℝ] V)‖ * ‖w‖ :=
    (L.symm : V →L[ℝ] V).le_opNorm w
  have hvw : ‖L.symm v‖ * ‖L.symm w‖ ≤
      (‖(L.symm : V →L[ℝ] V)‖ * ‖v‖) *
        (‖(L.symm : V →L[ℝ] V)‖ * ‖w‖) :=
    mul_le_mul hv hw (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hs : 0 ≤ heatScale34 t := by
    unfold heatScale34
    exact (Real.rpow_pos_of_pos ht _).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hvw (NNReal.coe_nonneg _)) hs)
    (heatC2Half_nonneg (V := V))

end LinearPull

end Poincare.Parabolic.Interior.Kernel
