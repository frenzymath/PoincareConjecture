import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.InteriorRegularityConeReconstruction
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Polar.Derivatives
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Actual Cartesian fields of the reconstructed cone

The true radial derivative and the angular derivative divided by radius
give the literal Cartesian fields. The angular radius cancels, leaving
no singular factor at the center in the actual L2 bound. Morrey ICM
1950, printed pp. 183-185, for Morgan--Tian Lemma 19.2, pp. 437-438;
M65 derivation 38, actual cone derivatives and energy.
-/

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace PoincareMT.M65Interior

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual Cartesian cone fields, expressed on the genuine polar
rectangle after cancelling the angular radius. Morrey ICM pp. 183-185;
MT Lemma 19.2, pp. 437-438; derivation 38. -/
noncomputable def coneCartesianField (g : EuclideanSpace ℝ (Fin 3) → E)
    (r : ℝ) (v0 : EuclideanSpace ℝ (Fin 3))
    (v d : ℝ → EuclideanSpace ℝ (Fin 3)) (s θ : ℝ) (i : Fin 2) : E :=
  r⁻¹ • (Proofs.M58.angularPoint θ i •
      fderiv ℝ g (coneCoordinates r v0 v s θ) (v θ - v0) +
    Proofs.M58.angularVector θ i •
      fderiv ℝ g (coneCoordinates r v0 v s θ) (d θ))

/-- The reconstructed radial column is its genuine ordinary derivative.
Morrey ICM pp. 183-185; MT Lemma 19.2, pp. 437-438; derivation 38. -/
theorem cone_reconstruction_radial {g : EuclideanSpace ℝ (Fin 3) → E}
    (r : ℝ) (v0 : EuclideanSpace ℝ (Fin 3)) (v : ℝ → EuclideanSpace ℝ (Fin 3))
    (s θ : ℝ) (hg : DifferentiableAt ℝ g (coneCoordinates r v0 v s θ)) :
    HasDerivAt (fun q => g (coneCoordinates r v0 v q θ))
      (r⁻¹ • fderiv ℝ g (coneCoordinates r v0 v s θ) (v θ - v0)) s := by
  simpa only [Function.comp_def, map_smul] using
    hg.hasFDerivAt.comp_hasDerivAt s (coneCoordinates_radial_hasDerivAt r v0 v s θ)

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual rotating frame preserves the sum of the two squared
column norms. Morrey ICM pp. 183-185; MT Lemma 19.2, pp. 437-438;
derivation 38, the literal cone energy calculation. -/
theorem coneCartesianField_norm_sq (g : EuclideanSpace ℝ (Fin 3) → E)
    (r : ℝ) (v0 : EuclideanSpace ℝ (Fin 3))
    (v d : ℝ → EuclideanSpace ℝ (Fin 3)) (s θ : ℝ) :
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

/-- The true derivative bound controls the actual Cartesian fields by
the circle increment and its original angular field. There is no
inverse polar radius in this bound. Morrey ICM pp. 183-185;
MT Lemma 19.2, pp. 437-438; derivation 38. -/
theorem coneCartesianField_norm_sq_le (g : EuclideanSpace ℝ (Fin 3) → E)
    (r : ℝ) (v0 : EuclideanSpace ℝ (Fin 3))
    (v d : ℝ → EuclideanSpace ℝ (Fin 3)) (s θ : ℝ) {K : ℝ}
    (hg : ‖fderiv ℝ g (coneCoordinates r v0 v s θ)‖ ≤ K) :
    (∑ i : Fin 2, ‖coneCartesianField g r v0 v d s θ i‖ ^ 2) ≤
      (r⁻¹) ^ 2 * K ^ 2 * (‖v θ - v0‖ ^ 2 + ‖d θ‖ ^ 2) := by
  let A := fderiv ℝ g (coneCoordinates r v0 v s θ)
  have hbound (z : EuclideanSpace ℝ (Fin 3)) : ‖A z‖ ^ 2 ≤ K ^ 2 * ‖z‖ ^ 2 := by
    have h := A.le_opNorm z |>.trans (mul_le_mul_of_nonneg_right hg (norm_nonneg z))
    simpa only [← sq, mul_pow] using mul_self_le_mul_self (norm_nonneg (A z)) h
  rw [coneCartesianField_norm_sq]
  calc
    _ ≤ (r⁻¹) ^ 2 * (K ^ 2 * ‖v θ - v0‖ ^ 2 + K ^ 2 * ‖d θ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add (hbound _) (hbound _)) (sq_nonneg _)
    _ = _ := by ring

end PoincareMT.M65Interior
