import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.ConeReconstruction

/-!
# Actual Cartesian cone fields in arbitrary dimension

The coordinate-dependent calculation from M65 `InteriorRegularityConeFields`
is generalized to a proper real Banach coordinate space. Its generic
AC composition, interpolation and polar transport lemmas are reused
from the independent authorized M65 closure. Source: Morrey ICM 1950,
pp. 183-185; M64 derivation `2026-09-26-general-half-cone.md`.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal InnerProductSpace

namespace PoincareMT.M64BoundaryCone

open M65Interior

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual Cartesian cone fields, expressed on the genuine polar rectangle after
cancelling the angular radius. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449; M64 derivation 2026-09-26-general-half-cone.md. -/
noncomputable def coneCartesianField (g : C → E)
    (r : ℝ) (v0 : C)
    (v d : ℝ → C) (s θ : ℝ) (i : Fin 2) : E :=
  r⁻¹ • (Proofs.M58.angularPoint θ i •
      fderiv ℝ g (coneCoordinates r v0 v s θ) (v θ - v0) +
    Proofs.M58.angularVector θ i •
      fderiv ℝ g (coneCoordinates r v0 v s θ) (d θ))

/-- The reconstructed radial column is its genuine ordinary derivative. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
theorem cone_reconstruction_radial {g : C → E}
    (r : ℝ) (v0 : C) (v : ℝ → C)
    (s θ : ℝ) (hg : DifferentiableAt ℝ g (coneCoordinates r v0 v s θ)) :
    HasDerivAt (fun q => g (coneCoordinates r v0 v q θ))
      (r⁻¹ • fderiv ℝ g (coneCoordinates r v0 v s θ) (v θ - v0)) s := by
  simpa only [Function.comp_def, map_smul] using
    hg.hasFDerivAt.comp_hasDerivAt s (coneCoordinates_radial_hasDerivAt r v0 v s θ)

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual rotating frame preserves the sum of the two squared column norms. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
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

/-- The true derivative bound controls the actual Cartesian fields by the circle increment
and its original angular field. There is no inverse polar radius in this bound. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
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

end PoincareMT.M64BoundaryCone
