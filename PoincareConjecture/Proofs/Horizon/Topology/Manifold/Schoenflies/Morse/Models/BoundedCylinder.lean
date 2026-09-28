import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.RadialGraph
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

private def boundedCylinderWeight (s : Real) : Real :=
  Real.smoothTransition (4 * s ^ 2 - 2)

private theorem boundedCylinderWeight_zero {s : Real} (hs : s ^ 2 ≤ 1 / 2) :
    boundedCylinderWeight s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem boundedCylinderWeight_one {s : Real} (hs : 3 / 4 ≤ s ^ 2) :
    boundedCylinderWeight s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private def boundedCylinderDenominator (s : Real) : Real :=
  (1 - boundedCylinderWeight s) * (1 - s ^ 2) + boundedCylinderWeight s * s ^ 2

private theorem boundedCylinderDenominator_quarter_le (s : Real) :
    1 / 4 ≤ boundedCylinderDenominator s := by
  have ha0 : 0 ≤ boundedCylinderWeight s := Real.smoothTransition.nonneg _
  have ha1 : boundedCylinderWeight s ≤ 1 := Real.smoothTransition.le_one _
  by_cases h0 : s ^ 2 ≤ 1 / 2
  · simp only [boundedCylinderDenominator, boundedCylinderWeight_zero h0,
      sub_zero, one_mul, zero_mul, add_zero]
    linarith
  by_cases h1 : 3 / 4 ≤ s ^ 2
  · simp only [boundedCylinderDenominator, boundedCylinderWeight_one h1,
      sub_self, zero_mul, one_mul, zero_add]
    linarith
  have hB := mul_nonneg (sub_nonneg.mpr ha1) (show 0 ≤ 1 - s ^ 2 - 1 / 4 by linarith)
  have hC := mul_nonneg ha0 (show 0 ≤ s ^ 2 - 1 / 4 by linarith)
  dsimp only [boundedCylinderDenominator]
  nlinarith

private theorem boundedCylinderDenominator_pos (s : Real) :
    0 < boundedCylinderDenominator s := by
  linarith [boundedCylinderDenominator_quarter_le s]

private theorem boundedCylinderDenominator_horizontal_le (s : Real) :
    1 - s ^ 2 ≤ boundedCylinderDenominator s := by
  by_cases h0 : s ^ 2 ≤ 1 / 2
  · simp [boundedCylinderDenominator, boundedCylinderWeight_zero h0]
  have ha0 : 0 ≤ boundedCylinderWeight s := Real.smoothTransition.nonneg _
  have h := mul_nonneg ha0 (show 0 ≤ 2 * s ^ 2 - 1 by linarith)
  dsimp only [boundedCylinderDenominator]
  nlinarith

def boundedCylinderRadius (v : E3) (p : S2) : Real :=
  (Real.sqrt (boundedCylinderDenominator (inner Real v (p : E3))))⁻¹

theorem boundedCylinderRadius_pos (v : E3) (p : S2) :
    0 < boundedCylinderRadius v p :=
  inv_pos.mpr (Real.sqrt_pos.mpr (boundedCylinderDenominator_pos _))

theorem boundedCylinderRadius_le_two (v : E3) (p : S2) :
    boundedCylinderRadius v p ≤ 2 := by
  have hs : 1 / 2 ≤ Real.sqrt (boundedCylinderDenominator (inner Real v (p : E3))) := by
    have h := boundedCylinderDenominator_quarter_le (inner Real v (p : E3))
    have heq := Real.sq_sqrt (boundedCylinderDenominator_pos (inner Real v (p : E3))).le
    nlinarith [Real.sqrt_nonneg (boundedCylinderDenominator (inner Real v (p : E3)))]
  dsimp only [boundedCylinderRadius]
  rw [← one_div, div_le_iff₀ (Real.sqrt_pos.mpr (boundedCylinderDenominator_pos _))]
  linarith

theorem contMDiff_boundedCylinderRadius (v : E3) :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (boundedCylinderRadius v) := by
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p : S2 => inner Real v (p : E3)) :=
    (innerSL Real v).contMDiff.comp (fun p => contMDiff_coe_sphere (n := 2) p)
  have ha : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (fun p : S2 => boundedCylinderWeight (inner Real v (p : E3))) :=
    Real.smoothTransition.contDiff.contMDiff.comp
      ((contMDiff_const.mul (hh.pow 2)).sub contMDiff_const)
  have hD : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (fun p : S2 => boundedCylinderDenominator (inner Real v (p : E3))) :=
    ((contMDiff_const.sub ha).mul (contMDiff_const.sub (hh.pow 2))).add
      (ha.mul (hh.pow 2))
  have hs : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (fun p : S2 => Real.sqrt (boundedCylinderDenominator (inner Real v (p : E3)))) := by
    intro p
    exact (Real.contDiffAt_sqrt (boundedCylinderDenominator_pos _).ne').contMDiffAt.comp p (hD p)
  exact hs.inv₀ (fun p => (Real.sqrt_pos.mpr (boundedCylinderDenominator_pos _)).ne')

theorem boundedCylinderRadius_of_abs_height_le (v : E3) (p : S2)
    (hp : |inner Real v (p : E3)| ≤ 1 / 2) :
    boundedCylinderRadius v p = (Real.sqrt (1 - inner Real v (p : E3) ^ 2))⁻¹ := by
  have hsq : inner Real v (p : E3) ^ 2 ≤ 1 / 2 := by
    have := (sq_le_sq₀ (abs_nonneg (inner Real v (p : E3)))
      (by norm_num : (0 : Real) ≤ 1 / 2)).mpr hp
    nlinarith [sq_abs (inner Real v (p : E3))]
  simp [boundedCylinderRadius, boundedCylinderDenominator, boundedCylinderWeight_zero hsq]

theorem boundedCylinderRadius_of_three_quarters_le_sq_height (v : E3) (p : S2)
    (hp : 3 / 4 ≤ inner Real v (p : E3) ^ 2) :
    boundedCylinderRadius v p = |inner Real v (p : E3)|⁻¹ := by
  simp [boundedCylinderRadius, boundedCylinderDenominator, boundedCylinderWeight_one hp,
    Real.sqrt_sq_eq_abs]

theorem norm_boundedCylinder_projection_le (v : E3) (hv : ‖v‖ = 1) (p : S2) :
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto
      (boundedCylinderRadius v p • (p : E3))‖ ≤ 1 := by
  have hvv : inner Real v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hpp : inner Real (p : E3) p = 1 := by simp
  have hproj : ‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ ^ 2 =
      1 - inner Real v (p : E3) ^ 2 := by
    change ‖((Hemisphere.Plane v).orthogonalProjectionOnto (p : E3) : E3)‖ ^ 2 = _
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton Real hv, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hvv, hpp, real_inner_comm (p : E3) v]
    ring
  have hnorm : ‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ ≤
      Real.sqrt (boundedCylinderDenominator (inner Real v (p : E3))) := by
    have hs := Real.sq_sqrt (boundedCylinderDenominator_pos (inner Real v (p : E3))).le
    have hh := boundedCylinderDenominator_horizontal_le (inner Real v (p : E3))
    nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)),
      Real.sqrt_nonneg (boundedCylinderDenominator (inner Real v (p : E3)))]
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (boundedCylinderRadius_pos v p)]
  calc
    _ ≤ boundedCylinderRadius v p *
        Real.sqrt (boundedCylinderDenominator (inner Real v (p : E3))) :=
      mul_le_mul_of_nonneg_left hnorm (boundedCylinderRadius_pos v p).le
    _ = 1 := inv_mul_cancel₀ (Real.sqrt_pos.mpr (boundedCylinderDenominator_pos _)).ne'

theorem abs_boundedCylinder_height_le (v : E3) (hv : ‖v‖ = 1) (p : S2) :
    |inner Real v (boundedCylinderRadius v p • (p : E3))| ≤ 2 := by
  have hh : |inner Real v (p : E3)| ≤ 1 := by
    simpa [hv] using abs_real_inner_le_norm v (p : E3)
  rw [inner_smul_right, abs_mul, abs_of_pos (boundedCylinderRadius_pos v p)]
  calc
    _ ≤ boundedCylinderRadius v p * 1 :=
      mul_le_mul_of_nonneg_left hh (boundedCylinderRadius_pos v p).le
    _ ≤ 2 := by simpa using boundedCylinderRadius_le_two v p

theorem exists_boundedCylinder_ambient (v : E3) (hv : ‖v‖ = 1) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∃ K : Set E3, IsCompact K ∧ ∀ x ∉ K, F x = x) ∧
      (∀ p : S2, F p = boundedCylinderRadius v p • (p : E3)) ∧
      (∀ p : S2, ‖(Hemisphere.Plane v).orthogonalProjectionOnto (F p)‖ ≤ 1) ∧
      (∀ p : S2, |inner Real v (F p)| ≤ 2) := by
  obtain ⟨F, hsupport, hF⟩ := exists_radial_sphere_extension (boundedCylinderRadius v)
    (contMDiff_boundedCylinderRadius v) (boundedCylinderRadius_pos v)
  refine ⟨F, hsupport, hF, ?_, ?_⟩
  · intro p
    rw [hF]
    exact norm_boundedCylinder_projection_le v hv p
  · intro p
    rw [hF]
    exact abs_boundedCylinder_height_le v hv p

end Poincare.Manifold.Schoenflies
