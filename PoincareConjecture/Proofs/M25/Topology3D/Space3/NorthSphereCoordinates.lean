import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereSmoothRestriction
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

noncomputable def northSphereVector (w : E2) : E3 :=
  heightCoordinates.symm ((2 / (1 + ‖w‖ ^ 2)) • w,
    (1 - ‖w‖ ^ 2) / (1 + ‖w‖ ^ 2))

theorem northSphereVector_norm (w : E2) : ‖northSphereVector w‖ = 1 := by
  have hD : 1 + ‖w‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hsq : ‖northSphereVector w‖ ^ 2 = 1 := by
    rw [northSphereVector, heightCoordinates_symm_norm_sq, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp [hD]
    ring
  nlinarith [norm_nonneg (northSphereVector w)]

noncomputable def northSpherePoint (w : E2) : UnitTwoSphere :=
  ⟨northSphereVector w, mem_sphere_zero_iff_norm.mpr (northSphereVector_norm w)⟩

theorem northSpherePoint_coordinates (w : E2) :
    heightCoordinates (northSpherePoint w : E3) =
      ((2 / (1 + ‖w‖ ^ 2)) • w, (1 - ‖w‖ ^ 2) / (1 + ‖w‖ ^ 2)) :=
  heightCoordinates.apply_symm_apply _

noncomputable def northSphereCoordinate (q : UnitTwoSphere) : E2 :=
  (1 + (heightCoordinates (q : E3)).2)⁻¹ • (heightCoordinates (q : E3)).1

def northSphereDomain : Set UnitTwoSphere :=
  {q | -1 < (heightCoordinates (q : E3)).2}

theorem northSpherePoint_mem_domain (w : E2) : northSpherePoint w ∈ northSphereDomain := by
  change -1 < (heightCoordinates (northSpherePoint w : E3)).2
  rw [northSpherePoint_coordinates]
  have hD : 0 < 1 + ‖w‖ ^ 2 := by positivity
  apply (lt_div_iff₀ hD).mpr
  linarith

theorem northSphereCoordinate_point (w : E2) :
    northSphereCoordinate (northSpherePoint w) = w := by
  rw [northSphereCoordinate, northSpherePoint_coordinates]
  dsimp only
  rw [smul_smul]
  have hD : 1 + ‖w‖ ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have he : 1 + (1 - ‖w‖ ^ 2) / (1 + ‖w‖ ^ 2) = 2 / (1 + ‖w‖ ^ 2) := by
    field_simp [hD]
    ring
  rw [he, inv_mul_cancel₀ (div_ne_zero (by norm_num) hD), one_smul]

theorem sphere_height_coordinates_sq (q : UnitTwoSphere) :
    ‖(heightCoordinates (q : E3)).1‖ ^ 2 + (heightCoordinates (q : E3)).2 ^ 2 = 1 := by
  rw [← heightCoordinates_norm_sq, norm_eq_of_mem_sphere q, one_pow]

theorem northSpherePoint_coordinate {q : UnitTwoSphere} (hq : q ∈ northSphereDomain) :
    northSpherePoint (northSphereCoordinate q) = q := by
  apply Subtype.ext
  apply heightCoordinates.injective
  rw [northSpherePoint_coordinates]
  let x := (heightCoordinates (q : E3)).1
  let z := (heightCoordinates (q : E3)).2
  have hz : 0 < 1 + z := by change -1 < z at hq; linarith
  have hunit : ‖x‖ ^ 2 + z ^ 2 = 1 := sphere_height_coordinates_sq q
  have hw : ‖northSphereCoordinate q‖ ^ 2 = ‖x‖ ^ 2 / (1 + z) ^ 2 := by
    change ‖(1 + z)⁻¹ • x‖ ^ 2 = _
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    ring
  have hD : 1 + ‖northSphereCoordinate q‖ ^ 2 = 2 / (1 + z) := by
    rw [hw]
    field_simp [hz.ne']
    nlinarith
  have hfactor : 2 / (2 / (1 + z)) * (1 + z)⁻¹ = 1 := by
    field_simp [hz.ne']
  apply Prod.ext
  · change (2 / (1 + ‖northSphereCoordinate q‖ ^ 2)) • ((1 + z)⁻¹ • x) = x
    rw [hD, smul_smul, hfactor, one_smul]
  · change (1 - ‖northSphereCoordinate q‖ ^ 2) /
      (1 + ‖northSphereCoordinate q‖ ^ 2) = z
    rw [hD, hw]
    field_simp [hz.ne']
    nlinarith

theorem northSphereVector_contDiff : ContDiff ℝ ∞ northSphereVector := by
  have hD : ContDiff ℝ ∞ (fun w : E2 => 1 + ‖w‖ ^ 2) :=
    contDiff_const.add (contDiff_id.norm_sq ℝ)
  have hn : ContDiff ℝ ∞ (fun w : E2 => 1 - ‖w‖ ^ 2) :=
    contDiff_const.sub (contDiff_id.norm_sq ℝ)
  exact heightCoordinates.symm.contDiff.comp
    ((contDiff_const.div hD (fun w => ne_of_gt (by positivity))).smul contDiff_id
      |>.prodMk (hn.div hD (fun w => ne_of_gt (by positivity))))

theorem northSpherePoint_contMDiff : ContMDiff 𝓘(ℝ, E2) (𝓡 2) ∞ northSpherePoint := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  exact northSphereVector_contDiff.contMDiff.codRestrict_sphere
    (fun w => mem_sphere_zero_iff_norm.mpr (northSphereVector_norm w))

theorem northSphereDomain_isOpen : IsOpen northSphereDomain :=
  isOpen_lt continuous_const
    ((heightCoordinates.continuous.comp continuous_subtype_val).snd)

theorem northSphereCoordinate_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ northSphereCoordinate northSphereDomain := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hC : ContMDiff (𝓡 2) 𝓘(ℝ, E2 × ℝ) ∞
      (fun q : UnitTwoSphere => heightCoordinates (q : E3)) :=
    heightCoordinates.contDiff.contMDiff.comp contMDiff_coe_sphere
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, E2) ∞
      (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).1) :=
    (contDiff_fst.contMDiff).comp hC
  have hz : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun q : UnitTwoSphere => 1 + (heightCoordinates (q : E3)).2) :=
    (contDiff_const.add contDiff_snd).contMDiff.comp hC
  intro q hq
  have hn : 1 + (heightCoordinates (q : E3)).2 ≠ 0 := by
    change -1 < (heightCoordinates (q : E3)).2 at hq
    linarith
  exact (((contDiffAt_inv ℝ hn).contMDiffAt.comp q (hz q)).smul (hf q)).contMDiffWithinAt

end PoincareConjecture.M25.Topology3D
