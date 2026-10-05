import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Geometry.CylinderGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Mathlib.StereographicMetric

/-!
# The actual sphere metric throughout a preferred chart

Morgan-Tian Definition 2.16, p. 30, used in the analytic neck estimates of
Theorem 12.28, pp. 323-324. The model metric in the frozen norm is written
explicitly in its actual stereographic chart, including off-center points.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.M35

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

/-- Definition 2.16, p. 30: the literal sphere metric has its stereographic
conformal factor at every point of the preferred chart. -/
theorem sphere_chart_pullback_inner_at (q : UnitTwoSphere)
    (p v w : EuclideanSpace ℝ (Fin 2)) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    inner ℝ
      (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1) (c.symm p)
        (mfderiv (𝓡 2) (𝓡 2) c.symm p v))
      (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1) (c.symm p)
        (mfderiv (𝓡 2) (𝓡 2) c.symm p w)) =
      16 / (‖p‖ ^ 2 + 4) ^ 2 * inner ℝ v w := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
    2 (ne_zero_of_mem_unit_sphere (-q))).repr
  let L := (ℝ ∙ (-q : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.comp
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hp : p ∈ c.target := by rw [sphere_chart_target]; trivial
  have hc : ContMDiffAt (𝓡 2) (𝓡 2) ∞ c.symm p :=
    (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) p hp).contMDiffAt
      (c.open_target.mem_nhds hp)
  have hinc : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun z : UnitTwoSphere => z.1) (c.symm p) :=
    (contMDiff_coe_sphere (m := ∞) (c.symm p)).mdifferentiableAt (by simp)
  have hd : DifferentiableAt ℝ (stereoInvFunAux (-q : EuclideanSpace ℝ (Fin 3)))
      (L p) :=
    (contDiff_stereoInvFunAux (m := ∞)).differentiable (by simp) (L p)
  have hfun : (fun p : EuclideanSpace ℝ (Fin 2) => (c.symm p).1) =
      stereoInvFunAux (-q : EuclideanSpace ℝ (Fin 3)) ∘ L := by
    funext p
    rfl
  have hmf := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
    p hinc (hc.mdifferentiableAt (by simp))
  have hderiv : (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1) (c.symm p)).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm p) =
        (fderiv ℝ (stereoInvFunAux (-q : EuclideanSpace ℝ (Fin 3))) (L p)).comp L := by
    rw [← hmf, mfderiv_eq_fderiv]
    change fderiv ℝ (fun p : EuclideanSpace ℝ (Fin 2) => (c.symm p).1) p = _
    rw [hfun]
    exact (hd.hasFDerivAt.comp p L.hasFDerivAt).fderiv
  change inner ℝ
    (((mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1) (c.symm p)).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm p)) v)
    (((mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1) (c.symm p)).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm p)) w) = _
  rw [hderiv]
  have horth (a : EuclideanSpace ℝ (Fin 2)) :
      inner ℝ (-q : EuclideanSpace ℝ (Fin 3)) (L a) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (U.symm a).property
  have hnorm : ‖(-q : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (-q).property
  change inner ℝ (fderiv ℝ (stereoInvFunAux _) (L p) (L v))
    (fderiv ℝ (stereoInvFunAux _) (L p) (L w)) = _
  rw [inner_fderiv_stereoInvFunAux _ _ _ _ hnorm (horth p) (horth v) (horth w)]
  have hLp : ‖L p‖ = ‖p‖ := U.symm.norm_map p
  have hLvw : inner ℝ (L v) (L w) = inner ℝ v w := U.symm.inner_map_map v w
  rw [hLp, hLvw]

/-- Definition 2.16, p. 30: the frozen cylinder Gram matrix has an explicit
positive sphere factor throughout its stereographic chart. -/
theorem roundCylinderGram_eq (u : ℝ) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) :
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p =
      Matrix.diagonal ![32 * (1 - u) / (‖p.1‖ ^ 2 + 4) ^ 2,
        32 * (1 - u) / (‖p.1‖ ^ 2 + 4) ^ 2, 1] := by
  ext i j
  have hcoeff : roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j =
      2 * (1 - u) * (16 / (‖p.1‖ ^ 2 + 4) ^ 2 *
        inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis j).1) +
        (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 :=
    congrArg (fun a : ℝ => 2 * (1 - u) * a +
      (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2)
      (sphere_chart_pullback_inner_at q p.1 _ _)
  rw [hcoeff]
  fin_cases i <;> fin_cases j <;>
    simp [roundCylinderCoordinateBasis, Matrix.diagonal, EuclideanSpace.inner_single_left] <;>
    ring

/-- Definition 2.16, p. 30: each actual model coefficient is its sphere
conformal factor times a fixed Euclidean pairing, plus the axial pairing. -/
theorem roundCylinderGram_apply (u : ℝ) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) (a b : Fin 3) :
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b =
      (32 * (1 - u) / (‖p.1‖ ^ 2 + 4) ^ 2) *
        inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 +
        (roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2 := by
  rw [roundCylinderGram_eq]
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.diagonal, roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left]

/-- Definition 2.16, p. 30: the inverse of the literal model Gram matrix
throughout the preferred chart, before the model singular time. -/
theorem roundCylinderGram_inv_eq {u : ℝ} (hu : u < 1) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) :
    (roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p)⁻¹ =
      Matrix.diagonal ![(‖p.1‖ ^ 2 + 4) ^ 2 / (32 * (1 - u)),
        (‖p.1‖ ^ 2 + 4) ^ 2 / (32 * (1 - u)), 1] := by
  rw [roundCylinderGram_eq]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal]
  have h : 1 - u ≠ 0 := by linarith
  have hd : ‖p.1‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal] <;> field_simp [h, hd]

/-- Definition 2.16, p. 30: every actual model metric coefficient is smooth
throughout its stereographic coordinate domain. -/
theorem contDiff_roundCylinderGram (u : ℝ) (q : UnitTwoSphere) (a b : Fin 3) :
    ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates =>
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) := by
  simp_rw [roundCylinderGram_apply]
  have hn : ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates => ‖p.1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_fst
  apply ContDiff.add _ contDiff_const
  apply ContDiff.mul _ contDiff_const
  exact contDiff_const.div ((hn.add contDiff_const).pow 2)
    (fun p => ne_of_gt (by positivity))

end PoincareMT.M35
