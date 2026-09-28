import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryConeReconstruction

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal InnerProductSpace

namespace PoincareConjecture.M64BoundaryCone

open M65Interior

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def coneCartesianField (g : C → E)
    (r : ℝ) (v0 : C)
    (v d : ℝ → C) (s θ : ℝ) (i : Fin 2) : E :=
  r⁻¹ • (Proofs.M58.angularPoint θ i •
      fderiv ℝ g (coneCoordinates r v0 v s θ) (v θ - v0) +
    Proofs.M58.angularVector θ i •
      fderiv ℝ g (coneCoordinates r v0 v s θ) (d θ))

theorem cone_reconstruction_radial {g : C → E}
    (r : ℝ) (v0 : C) (v : ℝ → C)
    (s θ : ℝ) (hg : DifferentiableAt ℝ g (coneCoordinates r v0 v s θ)) :
    HasDerivAt (fun q => g (coneCoordinates r v0 v q θ))
      (r⁻¹ • fderiv ℝ g (coneCoordinates r v0 v s θ) (v θ - v0)) s := by
  simpa only [Function.comp_def, map_smul] using
    hg.hasFDerivAt.comp_hasDerivAt s (coneCoordinates_radial_hasDerivAt r v0 v s θ)

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coneCartesianField_norm_sq (g : C → E)
    (r : ℝ) (v0 : C)
    (v d : ℝ → C) (s θ : ℝ) :
    (∑ i : Fin 2, ‖coneCartesianField g r v0 v d s θ i‖ ^ 2) =
      (r⁻¹) ^ 2 *
        (‖fderiv ℝ g (coneCoordinates r v0 v s θ) (v θ - v0)‖ ^ 2 +
          ‖fderiv ℝ g (coneCoordinates r v0 v s θ) (d θ)‖ ^ 2) := by
  simp only [Fin.sum_univ_two, coneCartesianField, Proofs.M58.angularPoint,
    Proofs.M58.angularVector, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_add_sq_real,
    real_inner_smul_left, real_inner_smul_right]
  calc
    _ = (r⁻¹) ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) *
        (‖fderiv ℝ g (coneCoordinates r v0 v s θ) (v θ - v0)‖ ^ 2 +
          ‖fderiv ℝ g (coneCoordinates r v0 v s θ) (d θ)‖ ^ 2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

theorem coneCartesianField_norm_sq_le (g : C → E)
    (r : ℝ) (v0 : C)
    (v d : ℝ → C) (s θ : ℝ) {K : ℝ}
    (hg : ‖fderiv ℝ g (coneCoordinates r v0 v s θ)‖ ≤ K) :
    (∑ i : Fin 2, ‖coneCartesianField g r v0 v d s θ i‖ ^ 2) ≤
      (r⁻¹) ^ 2 * K ^ 2 * (‖v θ - v0‖ ^ 2 + ‖d θ‖ ^ 2) := by
  let A := fderiv ℝ g (coneCoordinates r v0 v s θ)
  have hbound (z : C) : ‖A z‖ ^ 2 ≤ K ^ 2 * ‖z‖ ^ 2 := by
    have h := A.le_opNorm z |>.trans (mul_le_mul_of_nonneg_right hg (norm_nonneg z))
    simpa only [← sq, mul_pow] using mul_self_le_mul_self (norm_nonneg (A z)) h
  rw [coneCartesianField_norm_sq]
  calc
    _ ≤ (r⁻¹) ^ 2 * (K ^ 2 * ‖v θ - v0‖ ^ 2 + K ^ 2 * ‖d θ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add (hbound _) (hbound _)) (sq_nonneg _)
    _ = _ := by ring

end PoincareConjecture.M64BoundaryCone
