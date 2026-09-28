import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.SphereGram










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private theorem stereoInvFunAux_fderiv_apply
    (v x h : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (stereoInvFunAux v) x h =
      (‖x‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • h + (2 * inner ℝ x h) • v) +
      (-((‖x‖ ^ 2 + 4) ^ 2)⁻¹ * (2 * inner ℝ x h)) •
        ((4 : ℝ) • x + (‖x‖ ^ 2 - 4) • v) := by
  have hd : ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hsq : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ x) x := by
    simpa only [two_smul] using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hden := (hasFDerivAt_inv hd).comp x (hsq.add_const 4)
  have hnum := ((hasFDerivAt_id x).const_smul (4 : ℝ)).add
    ((hsq.sub_const 4).smul_const v)
  have heq := congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) => L h) (hden.smul hnum).fderiv
  change fderiv ℝ (stereoInvFunAux v) x h =
    (‖x‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • h + (2 * inner ℝ x h) • v) +
      ((2 * inner ℝ x h) * -((‖x‖ ^ 2 + 4) ^ 2)⁻¹) •
        ((4 : ℝ) • x + (‖x‖ ^ 2 - 4) • v) at heq
  simpa only [mul_comm] using heq

private theorem stereoInvFunAux_fderiv_inner
    (v x h k : EuclideanSpace ℝ (Fin 3))
    (hv : ‖v‖ = 1) (hx : inner ℝ v x = 0)
    (hh : inner ℝ v h = 0) (hk : inner ℝ v k = 0) :
    inner ℝ (fderiv ℝ (stereoInvFunAux v) x h)
      (fderiv ℝ (stereoInvFunAux v) x k) =
      (16 / (‖x‖ ^ 2 + 4) ^ 2) * inner ℝ h k := by
  have hd : ‖x‖ ^ 2 + 4 ≠ 0 := by positivity
  have hx' : inner ℝ x v = 0 := by rw [real_inner_comm, hx]
  have hh' : inner ℝ h v = 0 := by rw [real_inner_comm, hh]
  rw [stereoInvFunAux_fderiv_apply, stereoInvFunAux_fderiv_apply]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, hx, hx', hh', hk, real_inner_self_eq_norm_sq,
    hv, one_pow, mul_zero, add_zero, zero_add]
  rw [real_inner_comm h x]
  field_simp [hd]
  ring



noncomputable def sphereChartConformalFactor (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  16 / (‖x‖ ^ 2 + 4) ^ 2


theorem sphereChartConformalFactor_pos (x : EuclideanSpace ℝ (Fin 2)) :
    0 < sphereChartConformalFactor x := by
  unfold sphereChartConformalFactor
  positivity



theorem sphere_chart_inverse_inner_at (q : UnitTwoSphere)
    (x v w : EuclideanSpace ℝ (Fin 2)) :
    let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
    inner ℝ
      (mfderiv (𝓡 2) (𝓡 3) (fun y : UnitTwoSphere => y.1) (c.symm x)
        (mfderiv (𝓡 2) (𝓡 2) c.symm x v))
      (mfderiv (𝓡 2) (𝓡 3) (fun y : UnitTwoSphere => y.1) (c.symm x)
        (mfderiv (𝓡 2) (𝓡 2) c.symm x w)) =
      sphereChartConformalFactor x * inner ℝ v w := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
    (ne_zero_of_mem_unit_sphere (-q))).repr
  let A := (ℝ ∙ (↑(-q) : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.comp
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hderiv : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin 2) => (c.symm y).1)
      ((fderiv ℝ (stereoInvFunAux (↑(-q) : EuclideanSpace ℝ (Fin 3))) (A x)).comp A)
      x :=
    ((contDiff_stereoInvFunAux (v := (↑(-q) : EuclideanSpace ℝ (Fin 3)))
      (m := ∞)).differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
        A.hasFDerivAt
  have htarget : x ∈ c.target := by
    change x ∈ (stereographic' 2 (-q)).target
    rw [stereographic'_target]
    exact Set.mem_univ x
  have hsymm : MDifferentiableAt (𝓡 2) (𝓡 2) c.symm x :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ q) htarget
  have hcoe : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun y : UnitTwoSphere => y.1) (c.symm x) :=
    (contMDiff_coe_sphere (c.symm x)).mdifferentiableAt one_ne_zero
  have hcomp :
      (mfderiv (𝓡 2) (𝓡 3) (fun y : UnitTwoSphere => y.1) (c.symm x)).comp
        (mfderiv (𝓡 2) (𝓡 2) c.symm x) =
      (fderiv ℝ (stereoInvFunAux (↑(-q) : EuclideanSpace ℝ (Fin 3))) (A x)).comp A := by
    rw [← mfderiv_comp x hcoe hsymm, mfderiv_eq_fderiv]
    exact hderiv.fderiv
  change inner ℝ
    (((mfderiv (𝓡 2) (𝓡 3) (fun y : UnitTwoSphere => y.1) (c.symm x)).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm x)) v)
    (((mfderiv (𝓡 2) (𝓡 3) (fun y : UnitTwoSphere => y.1) (c.symm x)).comp
      (mfderiv (𝓡 2) (𝓡 2) c.symm x)) w) = _
  rw [hcomp]
  have horth (y : EuclideanSpace ℝ (Fin 2)) :
      inner ℝ (↑(-q) : EuclideanSpace ℝ (Fin 3)) (A y) = 0 := by
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (U.symm y).2
  have hnorm (y : EuclideanSpace ℝ (Fin 2)) : ‖A y‖ = ‖y‖ := U.symm.norm_map y
  have hinner : inner ℝ (A v) (A w) = inner ℝ v w := U.symm.inner_map_map v w
  change inner ℝ
    (fderiv ℝ (stereoInvFunAux (↑(-q) : EuclideanSpace ℝ (Fin 3))) (A x) (A v))
    (fderiv ℝ (stereoInvFunAux (↑(-q) : EuclideanSpace ℝ (Fin 3))) (A x) (A w)) = _
  simpa only [hnorm, hinner, sphereChartConformalFactor] using
    stereoInvFunAux_fderiv_inner (↑(-q)) (A x) (A v) (A w)
      (norm_eq_of_mem_sphere (-q)) (horth x) (horth v) (horth w)



theorem roundCylinderGram_chosen_chart (u : ℝ) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) :
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p =
      Matrix.diagonal ![2 * (1-u) * sphereChartConformalFactor p.1,
        2 * (1-u) * sphereChartConformalFactor p.1, 1] := by
  ext a b
  dsimp [roundCylinderGram, roundCylinderTensorCoefficient, EvolvingRoundCylinderMetric]
  rw [sphere_chart_inverse_inner_at]
  fin_cases a <;> fin_cases b <;>
    simp [roundCylinderCoordinateBasis, Matrix.diagonal, EuclideanSpace.inner_single_left]

end PoincareConjecture.Proofs.M28.NeckAnalysis
