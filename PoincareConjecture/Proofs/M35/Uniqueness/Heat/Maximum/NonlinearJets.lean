import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic











set_option autoImplicit false

noncomputable section

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def nonlinearSpaceJet (T : E × Z → ℝ) (x : E) (z : Z) : E →L[ℝ] ℝ :=
  (fderiv ℝ T (x, z)).comp (ContinuousLinearMap.inl ℝ E Z)

def nonlinearValueJet (T : E × Z → ℝ) (x : E) (z : Z) : Z →L[ℝ] ℝ :=
  (fderiv ℝ T (x, z)).comp (ContinuousLinearMap.inr ℝ E Z)


theorem nonlinear_field_fderiv {T : E × Z → ℝ} {X : E → Z} {x : E}
    (hT : DifferentiableAt ℝ T (x, X x)) (hX : DifferentiableAt ℝ X x) (v : E) :
    fderiv ℝ (fun y => T (y, X y)) x v =
      nonlinearSpaceJet T x (X x) v + nonlinearValueJet T x (X x) (fderiv ℝ X x v) := by
  have h := hT.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hX.hasFDerivAt)
  simp only [Function.comp_def, id_eq] at h
  rw [h.fderiv]
  change fderiv ℝ T (x, X x) (v, fderiv ℝ X x v) = _
  have hp : (v, fderiv ℝ X x v) = (v, (0 : Z)) + ((0 : E), fderiv ℝ X x v) := by
    simp
  rw [hp, map_add]
  rfl


theorem centered_covector_difference_le (A B : Z →L[ℝ] ℝ) (v w z : Z)
    {C L : ℝ} (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) (hAB : ‖A - B‖ ≤ L) :
    ‖A v - B w‖ ≤ C * ‖v - w‖ + (2 * C) * ‖w - z‖ + L * ‖z‖ := by
  have he : A v - B w = A (v - w) + (A - B) (w - z) + (A - B) z := by
    simp only [map_sub, sub_apply]
    abel
  rw [he]
  have hnorm : ‖A - B‖ ≤ 2 * C := (norm_sub_le A B).trans (by linarith)
  calc
    _ ≤ ‖A (v - w)‖ + ‖(A - B) (w - z)‖ + ‖(A - B) z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C * ‖v - w‖ + (2 * C) * ‖w - z‖ + L * ‖z‖ := by
      gcongr
      · exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
      · exact ((A - B).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
      · exact ((A - B).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hAB (norm_nonneg _))



theorem nonlinear_field_fderiv_sub_le {T : E × Z → ℝ} {X Y : E → Z} {x : E}
    (hTX : DifferentiableAt ℝ T (x, X x)) (hTY : DifferentiableAt ℝ T (x, Y x))
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x) (v : E) (z : Z)
    {C : ℝ}
    (hspace : ‖nonlinearSpaceJet T x (X x) v - nonlinearSpaceJet T x (Y x) v‖ ≤
      C * ‖X x - Y x‖)
    (hvalX : ‖nonlinearValueJet T x (X x)‖ ≤ C)
    (hvalY : ‖nonlinearValueJet T x (Y x)‖ ≤ C)
    (hval : ‖nonlinearValueJet T x (X x) - nonlinearValueJet T x (Y x)‖ ≤
      C * ‖X x - Y x‖) :
    ‖fderiv ℝ (fun y => T (y, X y)) x v - fderiv ℝ (fun y => T (y, Y y)) x v‖ ≤
      C * ‖X x - Y x‖ + C * ‖fderiv ℝ X x v - fderiv ℝ Y x v‖ +
        (2 * C) * ‖fderiv ℝ Y x v - z‖ + C * ‖X x - Y x‖ * ‖z‖ := by
  rw [nonlinear_field_fderiv hTX hX, nonlinear_field_fderiv hTY hY]
  have he : nonlinearSpaceJet T x (X x) v +
      nonlinearValueJet T x (X x) (fderiv ℝ X x v) -
        (nonlinearSpaceJet T x (Y x) v + nonlinearValueJet T x (Y x) (fderiv ℝ Y x v)) =
      (nonlinearSpaceJet T x (X x) v - nonlinearSpaceJet T x (Y x) v) +
        (nonlinearValueJet T x (X x) (fderiv ℝ X x v) -
          nonlinearValueJet T x (Y x) (fderiv ℝ Y x v)) := by ring
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hspace
    (centered_covector_difference_le _ _ _ _ z hvalX hvalY hval)).trans_eq (by ring))

end PoincareConjecture.M35.Uniqueness.Heat
