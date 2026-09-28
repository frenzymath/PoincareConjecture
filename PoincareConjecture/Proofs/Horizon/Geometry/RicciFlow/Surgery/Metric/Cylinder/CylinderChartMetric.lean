import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Cylinder.CylinderGram
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareConjecture.MetricSurgery

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem sphereChartEmbedding_inner_normal (theta : UnitTwoSphere) (p : E₂) :
    inner ℝ (sphereChartEmbedding theta p) (↑(-theta) : E₃) = 0 := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  apply Submodule.mem_orthogonal_singleton_iff_inner_left.mp
  exact ((OrthonormalBasis.fromOrthogonalSpanSingleton 2
    (ne_zero_of_mem_unit_sphere (-theta))).repr.symm p).property

theorem sphere_chart_inverse_formula (theta : UnitTwoSphere) (p : E₂) :
    ((chartAt E₂ theta).symm p : E₃) =
      (‖p‖ ^ 2 + 4)⁻¹ •
        ((4 : ℝ) • sphereChartEmbedding theta p + (‖p‖ ^ 2 - 4) • (↑(-theta) : E₃)) := by
  rw [sphere_chart_inverse_ambient, stereoInvFunAux_apply,
    (sphereChartEmbedding theta).norm_map]

theorem sphere_chart_inverse_fderiv (theta : UnitTwoSphere) (p v : E₂) :
    fderiv ℝ (fun x : E₂ => ((chartAt E₂ theta).symm x : E₃)) p v =
      (‖p‖ ^ 2 + 4)⁻¹ •
          ((4 : ℝ) • sphereChartEmbedding theta v +
            (2 * inner ℝ p v) • (↑(-theta) : E₃)) +
        (-(‖p‖ ^ 2 + 4) ^ (-2 : ℤ) * (2 * inner ℝ p v)) •
          ((4 : ℝ) • sphereChartEmbedding theta p +
            (‖p‖ ^ 2 - 4) • (↑(-theta) : E₃)) := by
  have hn := (hasStrictFDerivAt_norm_sq p).hasFDerivAt
  have hne : ‖p‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  have hi := (hasFDerivAt_inv hne).comp p (hn.add_const 4)
  have hnum := ((sphereChartEmbedding theta).toContinuousLinearMap.hasFDerivAt.const_smul
      (4 : ℝ)).add ((hn.sub_const 4).smul_const (↑(-theta) : E₃))
  have hd := hi.smul hnum
  have heq : (fun x : E₂ => ((chartAt E₂ theta).symm x : E₃)) =
      fun x => (‖x‖ ^ 2 + 4)⁻¹ •
        ((4 : ℝ) • sphereChartEmbedding theta x + (‖x‖ ^ 2 - 4) • (↑(-theta) : E₃)) :=
    funext (sphere_chart_inverse_formula theta)
  have hv := congrArg (fun L : E₂ →L[ℝ] E₃ => L v) hd.fderiv
  rw [heq]
  convert hv using 1
  all_goals
    first
    | apply congrArg (fun f : E₂ → E₃ => fderiv ℝ f p v)
      funext x
      simp
    | simp [Pi.smul_apply, Pi.add_apply, zpow_neg,
        mul_comm, mul_assoc]

theorem sphere_chart_inverse_fderiv_inner (theta : UnitTwoSphere) (p v w : E₂) :
    inner ℝ
      (fderiv ℝ (fun x : E₂ => ((chartAt E₂ theta).symm x : E₃)) p v)
      (fderiv ℝ (fun x : E₂ => ((chartAt E₂ theta).symm x : E₃)) p w) =
        (16 / (‖p‖ ^ 2 + 4) ^ 2) * inner ℝ v w := by
  have hnormal : inner ℝ (↑(-theta) : E₃) (↑(-theta) : E₃) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere (-theta)]
    norm_num
  have horth (a : E₂) : inner ℝ (↑(-theta) : E₃) (sphereChartEmbedding theta a) = 0 := by
    rw [real_inner_comm, sphereChartEmbedding_inner_normal]
  have hne : ‖p‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  rw [sphere_chart_inverse_fderiv, sphere_chart_inverse_fderiv]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    (sphereChartEmbedding theta).inner_map_map, sphereChartEmbedding_inner_normal,
    horth, hnormal, real_inner_self_eq_norm_sq]
  rw [real_inner_comm v p, real_inner_comm w p]
  simp only [zpow_neg, zpow_ofNat]
  field_simp
  ring

theorem sphere_chart_differential_inner_at (theta : UnitTwoSphere) (p v w : E₂) :
    inner ℝ (E := E₃)
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm p) (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm p v))
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm p) (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm p w)) =
      (16 / (‖p‖ ^ 2 + 4) ^ 2) * inner ℝ v w := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  have hp : p ∈ (chartAt E₂ theta).target := by
    change p ∈ (stereographic' 2 (-theta)).target
    simp
  have hc := mdifferentiableAt_atlas_symm (I := 𝓡 2) (chart_mem_atlas _ theta) hp
  have hi := (contMDiff_coe_sphere (n := 2) (m := ∞)
    ((chartAt E₂ theta).symm p)).mdifferentiableAt (by simp)
  have hpoint (z : E₂) :
      mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm p) (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm p z) =
      fderiv ℝ (fun x : E₂ => ((chartAt E₂ theta).symm x : E₃)) p z := by
    have hcomp := mfderiv_comp p hi hc
    have hval := congrArg (fun L => L z) hcomp
    rw [mfderiv_eq_fderiv] at hval
    exact hval.symm
  rw [hpoint, hpoint]
  exact sphere_chart_inverse_fderiv_inner theta p v w

theorem roundCylinderGram_chart (theta : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    roundCylinderGram 0 (chartAt E₂ theta) p =
      Matrix.diagonal ![(32 / (‖p.1‖ ^ 2 + 4) ^ 2 : ℝ),
        32 / (‖p.1‖ ^ 2 + 4) ^ 2, 1] := by
  ext i j
  change 2 * (1 - (0 : ℝ)) * inner ℝ (E := E₃)
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm p.1)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm p.1
          (roundCylinderCoordinateBasis i).1))
      (mfderiv (𝓡 2) (𝓡 3) (fun q : UnitTwoSphere => q.1)
        ((chartAt E₂ theta).symm p.1)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm p.1
          (roundCylinderCoordinateBasis j).1)) +
      (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 = _
  rw [sphere_chart_differential_inner_at]
  fin_cases i <;> fin_cases j <;>
    simp [roundCylinderCoordinateBasis, Matrix.diagonal,
      EuclideanSpace.basisFun, EuclideanSpace.inner_single_left] <;> ring

end PoincareConjecture.MetricSurgery
