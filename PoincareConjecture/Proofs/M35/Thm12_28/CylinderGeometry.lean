import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Tactic










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩


theorem sphere_chart_center (q : UnitTwoSphere) :
    chartAt (EuclideanSpace ℝ (Fin 2)) q q = 0 := by
  change stereographic' 2 (-q) q = 0
  simp only [stereographic', OpenPartialHomeomorph.trans_apply]
  rw [stereographic_neg_apply]
  change (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
    2 (ne_zero_of_mem_unit_sphere (-q))).repr 0 = 0
  exact map_zero _


theorem sphere_chart_target (q : UnitTwoSphere) :
    (chartAt (EuclideanSpace ℝ (Fin 2)) q).target = univ :=
  stereographic'_target (-q)



theorem sphere_chart_pullback_inner (q : UnitTwoSphere)
    (v w : EuclideanSpace ℝ (Fin 2)) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    inner ℝ
      (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1) (c.symm 0)
        (mfderiv (𝓡 2) (𝓡 2) c.symm 0 v))
      (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1) (c.symm 0)
        (mfderiv (𝓡 2) (𝓡 2) c.symm 0 w)) = inner ℝ v w := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
    2 (ne_zero_of_mem_unit_sphere (-q))).repr
  have hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ c.target := by
    rw [sphere_chart_target]
    trivial
  have hc : ContMDiffAt (𝓡 2) (𝓡 2) ∞ c.symm 0 := by
    exact (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) 0 hzero).contMDiffAt
      (c.open_target.mem_nhds hzero)
  have hinc : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun z : UnitTwoSphere => z.1) (c.symm 0) :=
    (contMDiff_coe_sphere (m := ∞) (c.symm 0)).mdifferentiableAt (by simp)
  have hd : HasFDerivAt
      (stereoInvFunAux (-q : EuclideanSpace ℝ (Fin 3)) ∘
        (Subtype.val : (ℝ ∙ (-q : EuclideanSpace ℝ (Fin 3)))ᗮ →
          EuclideanSpace ℝ (Fin 3)))
      (ℝ ∙ (-q : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL (U.symm 0) := by
    convert! hasFDerivAt_stereoInvFunAux_comp_coe (-q : EuclideanSpace ℝ (Fin 3)) using 1
    rw [show U.symm 0 = 0 from map_zero U.symm]
    rfl
  have hcomp := (hd.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  have hfun : (fun p : EuclideanSpace ℝ (Fin 2) => (c.symm p).1) =
      (stereoInvFunAux (-q : EuclideanSpace ℝ (Fin 3)) ∘ Subtype.val) ∘ U.symm := by
    funext p
    rfl
  have hmf := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
    0 hinc (hc.mdifferentiableAt (by simp))
  have hderiv : (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1) (c.symm 0)).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm 0) =
        (ℝ ∙ (-q : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.comp
          U.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    rw [← hmf]
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (fun p : EuclideanSpace ℝ (Fin 2) => (c.symm p).1) 0 = _
    rw [hfun]
    exact hcomp
  change inner ℝ
    (((mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1) (c.symm 0)).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm 0)) v)
    (((mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1) (c.symm 0)).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm 0)) w) = _
  rw [hderiv]
  exact U.symm.inner_map_map v w



theorem roundCylinderGram_center (u : ℝ) (q : UnitTwoSphere) (s : ℝ) :
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s) =
      Matrix.diagonal ![2 * (1 - u), 2 * (1 - u), 1] := by
  rw [sphere_chart_center]
  ext i j
  have hcoeff : roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) (0, s) i j =
      2 * (1 - u) * inner ℝ (roundCylinderCoordinateBasis i).1
        (roundCylinderCoordinateBasis j).1 +
        (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 :=
    congrArg (fun a : ℝ => 2 * (1 - u) * a +
      (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2)
      (sphere_chart_pullback_inner q _ _)
  rw [hcoeff]
  fin_cases i <;> fin_cases j <;>
    simp [roundCylinderCoordinateBasis, Matrix.diagonal,
      EuclideanSpace.inner_single_left]



theorem roundCylinderGram_inv_center {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) :
    (roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q q, s))⁻¹ =
      Matrix.diagonal ![(2 * (1 - u))⁻¹, (2 * (1 - u))⁻¹, 1] := by
  rw [roundCylinderGram_center]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  have h : 1 - u ≠ 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal] <;> field_simp [h]

end PoincareConjecture.M35
