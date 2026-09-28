import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

noncomputable def sphereChartEmbedding (theta : UnitTwoSphere) : E₂ →ₗᵢ[ℝ] E₃ :=
  letI : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  (ℝ ∙ (↑(-theta) : E₃))ᗮ.subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2
      (ne_zero_of_mem_unit_sphere (-theta))).repr.symm.toLinearIsometry

theorem sphere_chart_center_zero (theta : UnitTwoSphere) :
    chartAt E₂ theta theta = 0 := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  change stereographic' 2 (-theta) theta = 0
  change (OrthonormalBasis.fromOrthogonalSpanSingleton 2
    (ne_zero_of_mem_unit_sphere (-theta))).repr
      (stereographic (norm_eq_of_mem_sphere (-theta)) theta) = 0
  rw [stereographic_neg_apply, map_zero]

theorem sphere_chart_inverse_ambient (theta : UnitTwoSphere) (p : E₂) :
    ((chartAt E₂ theta).symm p : E₃) =
      stereoInvFunAux (↑(-theta) : E₃) (sphereChartEmbedding theta p) := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  change ((stereographic' 2 (-theta)).symm p : E₃) =
    stereoInvFunAux (↑(-theta) : E₃)
      ((OrthonormalBasis.fromOrthogonalSpanSingleton 2
        (ne_zero_of_mem_unit_sphere (-theta))).repr.symm p : E₃)
  rw [stereographic'_symm_apply, stereoInvFunAux_apply, smul_add]

set_option backward.isDefEq.respectTransparency false in
theorem sphere_chart_inverse_hasFDerivAt (theta : UnitTwoSphere) :
    HasFDerivAt (fun p : E₂ => ((chartAt E₂ theta).symm p : E₃))
      (sphereChartEmbedding theta).toContinuousLinearMap 0 := by
  have houter : HasFDerivAt (stereoInvFunAux (↑(-theta) : E₃))
      (ContinuousLinearMap.id ℝ E₃) ((sphereChartEmbedding theta).toContinuousLinearMap 0) := by
    simpa only [map_zero] using hasFDerivAt_stereoInvFunAux (↑(-theta) : E₃)
  have h := houter.comp (0 : E₂)
    (sphereChartEmbedding theta).toContinuousLinearMap.hasFDerivAt
  have heq : (fun p : E₂ => ((chartAt E₂ theta).symm p : E₃)) =
      stereoInvFunAux (↑(-theta) : E₃) ∘
        (sphereChartEmbedding theta).toContinuousLinearMap := by
    funext p
    exact sphere_chart_inverse_ambient theta p
  rw [heq]
  simpa only [map_zero, ContinuousLinearMap.id_comp] using h

set_option backward.isDefEq.respectTransparency false in
theorem sphere_chart_differential_inner (theta : UnitTwoSphere) (v w : E₂) :
    inner ℝ (E := E₃)
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm 0) (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm 0 v))
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm 0) (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm 0 w)) =
      inner ℝ v w := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  have hzero : (0 : E₂) ∈ (chartAt E₂ theta).target := by
    change (0 : E₂) ∈ (stereographic' 2 (-theta)).target
    simp
  have hc := mdifferentiableAt_atlas_symm (I := 𝓡 2) (chart_mem_atlas _ theta) hzero
  have hi := (contMDiff_coe_sphere (n := 2) (m := ∞)
    ((chartAt E₂ theta).symm 0)).mdifferentiableAt
    (by simp)
  have hpoint (z : E₂) :
      mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm 0) (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm 0 z) =
      sphereChartEmbedding theta z := by
    have hcomp := mfderiv_comp (0 : E₂) hi hc
    have hval := congrArg (fun L => L z) hcomp
    rw [mfderiv_eq_fderiv] at hval
    change fderiv ℝ (fun p : E₂ => ((chartAt E₂ theta).symm p : E₃)) 0 z = _ at hval
    rw [(sphere_chart_inverse_hasFDerivAt theta).fderiv] at hval
    exact hval.symm
  rw [hpoint, hpoint]
  exact (sphereChartEmbedding theta).inner_map_map v w

set_option backward.isDefEq.respectTransparency false in
theorem roundCylinderGram_center (theta : UnitTwoSphere) (s : ℝ) :
    roundCylinderGram 0 (chartAt E₂ theta) (chartAt E₂ theta theta, s) =
      Matrix.diagonal ![(2 : ℝ), 2, 1] := by
  rw [sphere_chart_center_zero]
  ext i j
  change 2 * (1 - (0 : ℝ)) * inner ℝ (E := E₃)
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm 0)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm 0
          (roundCylinderCoordinateBasis i).1))
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm 0)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm 0
          (roundCylinderCoordinateBasis j).1)) +
      (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 = _
  rw [sphere_chart_differential_inner]
  fin_cases i <;> fin_cases j <;>
    norm_num [roundCylinderCoordinateBasis, Matrix.diagonal,
      EuclideanSpace.basisFun, EuclideanSpace.inner_single_left]

theorem roundCylinderGram_center_inv (theta : UnitTwoSphere) (s : ℝ) :
    (roundCylinderGram 0 (chartAt E₂ theta) (chartAt E₂ theta theta, s))⁻¹ =
      Matrix.diagonal ![(1 / 2 : ℝ), 1 / 2, 1] := by
  apply Matrix.inv_eq_right_inv
  rw [roundCylinderGram_center]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal]

end PoincareConjecture.M36
