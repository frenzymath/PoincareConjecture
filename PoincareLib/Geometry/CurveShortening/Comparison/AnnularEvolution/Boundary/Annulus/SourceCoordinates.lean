import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Modulus.ComplexEquation
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Supported.RectangleAdmission

/-! Literal boundary source coordinates for the two faces of the
annulus. The horizontal scale is the actual positive modulus; the
upper face reverses the radial coordinate.
Source: MT Lemma 19.15, pp. 447-449; M64 finite collar derivation. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Complex Metric
open scoped ContDiff

namespace PoincareMT.M64

/-- The actual oriented linear part of an annular boundary coordinate. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
def annulusBoundaryLinear (r : ℝ) (hr : r ≠ 0) (upper : Bool) : ℂ ≃L[ℝ] LoopPlane where
  toFun z := annulusPoint (r * z.re) (if upper then -z.im else z.im)
  invFun p := (r⁻¹ * p 0 : ℝ) + (if upper then -(p 1) else p 1 : ℝ) * I
  map_add' z w := by
    cases upper <;> ext i <;> fin_cases i <;> simp [annulusPoint, mul_add, add_comm]
  map_smul' c z := by
    cases upper <;> ext i <;> fin_cases i <;> simp [annulusPoint, mul_left_comm]
  left_inv z := by
    cases upper <;> apply Complex.ext <;> simp [annulusPoint, hr]
  right_inv p := by
    cases upper <;> ext i <;> fin_cases i <;> simp [annulusPoint, hr]
  continuous_toFun := by
    cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      unfold annulusPoint <;> fun_prop
  continuous_invFun := by
    cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop

/-- The actual horizontal column carries exactly the modulus. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem annulusBoundaryLinear_one (r : ℝ) (hr : r ≠ 0) (upper : Bool) :
    annulusBoundaryLinear r hr upper 1 = r • EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
  cases upper <;> ext i <;> fin_cases i <;>
    simp [annulusBoundaryLinear, annulusPoint, EuclideanSpace.basisFun_apply]

/-- The actual radial column has the orientation of the selected face. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem annulusBoundaryLinear_I (r : ℝ) (hr : r ≠ 0) (upper : Bool) :
    annulusBoundaryLinear r hr upper I = if upper then
      -EuclideanSpace.basisFun (Fin 2) ℝ 1 else EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
  cases upper <;> ext i <;> fin_cases i <;>
    simp [annulusBoundaryLinear, annulusPoint, EuclideanSpace.basisFun_apply]

/-- The actual affine coordinate centered at either radial face. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
def annulusBoundarySource (r : ℝ) (hr : r ≠ 0) (upper : Bool) (x : ℝ) (z : ℂ) : LoopPlane :=
  annulusPoint x (if upper then 1 else 0) + annulusBoundaryLinear r hr upper z

/-- The source formula keeps the original angular label. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem annulusBoundarySource_apply (r : ℝ) (hr : r ≠ 0) (upper : Bool) (x : ℝ) (z : ℂ) :
    annulusBoundarySource r hr upper x z =
      annulusPoint (x + r * z.re) (if upper then 1 - z.im else z.im) := by
  cases upper <;> ext i <;> fin_cases i <;>
    simp [annulusBoundarySource, annulusBoundaryLinear, annulusPoint, sub_eq_add_neg]

/-- The center and diameter are the literal original boundary points. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem annulusBoundarySource_real (r : ℝ) (hr : r ≠ 0) (upper : Bool) (x t : ℝ) :
    annulusBoundarySource r hr upper x (t : ℂ) =
      annulusPoint (x + r * t) (if upper then 1 else 0) := by
  rw [annulusBoundarySource_apply]
  cases upper <;> simp

/-- Sufficiently small closed half disks map to the actual annular rectangle. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem annulusBoundarySource_mapsTo_closed {r R x : ℝ} (hr : 0 < r)
    (hR : R < 1) (hx : r * R < x) (hP : x + r * R < curvePeriod) (upper : Bool) :
    MapsTo (annulusBoundarySource r hr.ne' upper x)
      (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) m64AnnulusDomain := by
  intro z hz
  have hn : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz.1
  have hre := abs_le.mp (z.abs_re_le_norm.trans hn)
  have him := (le_abs_self z.im).trans (z.abs_im_le_norm.trans hn)
  have hy : 0 ≤ z.im := hz.2
  have hlo : 0 ≤ x + r * z.re := by nlinarith [hre.1]
  have hhi : x + r * z.re ≤ curvePeriod := by nlinarith [hre.2]
  rw [annulusBoundarySource_apply]
  cases upper
  · exact ⟨hlo, hhi, hy, him.trans hR.le⟩
  · exact ⟨hlo, hhi, (show 0 ≤ 1 - z.im by linarith), (show 1 - z.im ≤ 1 by linarith)⟩

/-- Interior half-disk points map to the genuine open annular rectangle. Source:
Morgan--Tian (2007), Lemma 19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem annulusBoundarySource_mapsTo_open {r R x : ℝ} (hr : 0 < r)
    (hR : R < 1) (hx : r * R < x) (hP : x + r * R < curvePeriod) (upper : Bool) :
    MapsTo (annulusBoundarySource r hr.ne' upper x)
      (ball (0 : ℂ) R ∩ {z | 0 < z.im}) m64AnnulusInterior := by
  intro z hz
  have hn : ‖z‖ < R := mem_ball_zero_iff.mp hz.1
  have hre := abs_le.mp (z.abs_re_le_norm.trans hn.le)
  have him := (le_abs_self z.im).trans (z.abs_im_le_norm.trans hn.le)
  have hy : 0 < z.im := hz.2
  have hlo : 0 < x + r * z.re := by nlinarith [hre.1]
  have hhi : x + r * z.re < curvePeriod := by nlinarith [hre.2]
  rw [annulusBoundarySource_apply, mem_m64AnnulusInterior_iff]
  cases upper
  · exact ⟨hlo, hhi, hy, him.trans_lt hR⟩
  · exact ⟨hlo, hhi, (show 0 < 1 - z.im by linarith), (show 1 - z.im < 1 by linarith)⟩

end PoincareMT.M64
