import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationConjugate











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

private abbrev Plane := EuclideanSpace ℝ (Fin 2)



def firstCoordinateGradient (g : RiemannianMetric 2 Plane) (D : LeviCivitaData g)
    (x : Plane) : Plane := D.gradient (fun y : Plane => y 0) x



def conjugateMetricForm (g : RiemannianMetric 2 Plane) (D : LeviCivitaData g)
    (x : Plane) : Plane →L[ℝ] ℝ :=
  rotatedFlux
    (fun y => g.pullbackVolumeDensity id y * firstCoordinateGradient g D y 0)
    (fun y => g.pullbackVolumeDensity id y * firstCoordinateGradient g D y 1) x



theorem inner_firstCoordinateGradient (g : RiemannianMetric 2 Plane)
    (D : LeviCivitaData g) (x v : Plane) :
    g.inner x (firstCoordinateGradient g D x) v = v 0 := by
  rw [firstCoordinateGradient, D.inner_gradient]
  have hderiv : fderiv ℝ (fun y : Plane => y 0) x = EuclideanSpace.proj 0 :=
    (show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0).fderiv
  simp only [mvfderiv, mfderiv_eq_fderiv, hderiv, NormedSpace.fromTangentSpace]
  rfl



theorem firstCoordinateGradient_zero_pos (g : RiemannianMetric 2 Plane)
    (D : LeviCivitaData g) (x : Plane) : 0 < firstCoordinateGradient g D x 0 := by
  have hne : firstCoordinateGradient g D x ≠ 0 := by
    intro h
    have he := inner_firstCoordinateGradient g D x (EuclideanSpace.single 0 1)
    rw [h] at he
    norm_num [PiLp.single_apply] at he
  rw [← inner_firstCoordinateGradient g D x (firstCoordinateGradient g D x)]
  exact g.pos x _ hne



theorem plane_metric_expand (g : RiemannianMetric 2 Plane) (x v w : Plane) :
    g.inner x v w =
      g.inner x (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) * v 0 * w 0 +
      g.inner x (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) * (v 0 * w 1 + v 1 * w 0) +
      g.inner x (EuclideanSpace.basisFun (Fin 2) ℝ 1)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) * v 1 * w 1 := by
  have hexp (z : Plane) : z = z 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      z 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    simpa only [Fin.sum_univ_two, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
      using ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.sum_repr z).symm
  conv_lhs => rw [hexp v, hexp w]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [g.symm x (EuclideanSpace.basisFun (Fin 2) ℝ 1)
    (EuclideanSpace.basisFun (Fin 2) ℝ 0)]
  ring




theorem metric_eq_conjugate_coordinates (g : RiemannianMetric 2 Plane)
    (D : LeviCivitaData g) (x v w : Plane) :
    g.inner x v w = (firstCoordinateGradient g D x 0)⁻¹ *
      (v 0 * w 0 + conjugateMetricForm g D x v * conjugateMetricForm g D x w) := by
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let a := g.inner x (e 0) (e 0)
  let b := g.inner x (e 0) (e 1)
  let c := g.inner x (e 1) (e 1)
  let p := firstCoordinateGradient g D x
  let rho := g.pullbackVolumeDensity id x
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h0 : a * p 0 + b * p 1 = 1 := by
    have h := inner_firstCoordinateGradient g D x (e 0)
    rw [plane_metric_expand] at h
    simpa only [e, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      ite_true, h10, ite_false,
      mul_one, mul_zero, add_zero, zero_add, a, b, p] using h
  have h1 : b * p 0 + c * p 1 = 0 := by
    have h := inner_firstCoordinateGradient g D x (e 1)
    rw [plane_metric_expand] at h
    simpa only [e, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      ite_true, h01, ite_false,
      mul_one, mul_zero, add_zero, zero_add, b, c, p] using h
  have hrho : rho ^ 2 = a * c - b ^ 2 := by
    have hrhop := (g.contDiffAt_pullbackVolumeDensity (f := id) (x := x)
      contMDiffAt_id (by simpa using Function.injective_id)).2
    have hrhoe : rho = Real.sqrt (a * c - b ^ 2) := by
      simp only [rho, RiemannianMetric.pullbackVolumeDensity, mfderiv_id,
        Matrix.det_fin_two, Matrix.of_apply]
      change Real.sqrt (a * c - b * g.inner x (e 1) (e 0)) = _
      rw [g.symm x (e 1) (e 0)]
      simp only [b, pow_two]
    change 0 < rho at hrhop
    rw [hrhoe] at hrhop ⊢
    exact Real.sq_sqrt (Real.sqrt_pos.mp hrhop).le
  have hp0 : rho ^ 2 * p 0 = c := by
    rw [hrho]
    linear_combination c * h0 - b * h1
  have hp1 : rho ^ 2 * p 1 = -b := by
    rw [hrho]
    linear_combination a * h1 - b * h0
  have ha : a * p 0 = 1 + rho ^ 2 * (p 1) ^ 2 := by
    linear_combination h0 - p 1 * hp1
  have hb : b * p 0 = -(rho ^ 2 * p 0 * p 1) := by
    linear_combination p 0 * hp1
  have hc : c * p 0 = rho ^ 2 * (p 0) ^ 2 := by
    linear_combination -p 0 * hp0
  rw [eq_inv_mul_iff_mul_eq₀ (firstCoordinateGradient_zero_pos g D x).ne',
    plane_metric_expand]
  change p 0 * (a * v 0 * w 0 + b * (v 0 * w 1 + v 1 * w 0) +
    c * v 1 * w 1) = _
  have homega (z : Plane) : conjugateMetricForm g D x z =
      rho * (-(p 1) * z 0 + p 0 * z 1) := by
    simp only [conjugateMetricForm, rotatedFlux, add_apply, smul_apply,
      smul_eq_mul, EuclideanSpace.coe_proj, rho, p]
    ring
  rw [homega, homega]
  linear_combination v 0 * w 0 * ha + (v 0 * w 1 + v 1 * w 0) * hb +
    v 1 * w 1 * hc

end PoincareConjecture.M60

end
