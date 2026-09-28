import PoincareConjecture.Proofs.M60.Mathlib.UniformizationPrimitives
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace PoincareConjecture.M60

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem plane_form_apply (L : Plane →L[ℝ] ℝ) (v : Plane) :
    L v = L (EuclideanSpace.basisFun (Fin 2) ℝ 0) * v 0 +
      L (EuclideanSpace.basisFun (Fin 2) ℝ 1) * v 1 := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_add, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    Fin.sum_univ_two, mul_comm] using h.symm

def rotatedFlux (A B : Plane → ℝ) (x : Plane) : Plane →L[ℝ] ℝ :=
  -(B x) • EuclideanSpace.proj 0 + A x • EuclideanSpace.proj 1

theorem exists_conjugate_of_divergence_zero
    {A B : Plane → ℝ} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {S : Set Plane} (hS : StarConvex ℝ 0 S)
    (hdiv : ∀ x ∈ S,
      fderiv ℝ A x (EuclideanSpace.basisFun (Fin 2) ℝ 0) +
        fderiv ℝ B x (EuclideanSpace.basisFun (Fin 2) ℝ 1) = 0) :
    ∃ V : Plane → ℝ, ContDiff ℝ ∞ V ∧
      ∀ x ∈ S, HasFDerivAt V (rotatedFlux A B x) x := by
  have hs : ContDiff ℝ ∞ (rotatedFlux A B) :=
    (hB.neg.smul contDiff_const).add (hA.smul contDiff_const)
  refine ⟨radialPrimitive (rotatedFlux A B), radialPrimitive_contDiff hs, ?_⟩
  intro x hx
  apply hasFDerivAt_radialPrimitive hs hS ?_ hx
  intro y hy v w
  have hd (v w : Plane) :
      fderiv ℝ (rotatedFlux A B) y v w =
        -(fderiv ℝ B y v) * w 0 + fderiv ℝ A y v * w 1 := by
    have h := (((hB.differentiable (by simp) y).hasFDerivAt.neg.smul_const
      (show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0)).add
      ((hA.differentiable (by simp) y).hasFDerivAt.smul_const
        (show Plane →L[ℝ] ℝ from EuclideanSpace.proj 1))).fderiv
    have he := congrArg (fun L : Plane →L[ℝ] Plane →L[ℝ] ℝ => L v w) h
    simpa only [rotatedFlux, add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul, neg_apply, EuclideanSpace.coe_proj] using! he
  rw [hd, hd, plane_form_apply (fderiv ℝ B y) v,
    plane_form_apply (fderiv ℝ A y) v, plane_form_apply (fderiv ℝ B y) w,
    plane_form_apply (fderiv ℝ A y) w]
  linear_combination (v 0 * w 1 - v 1 * w 0) * hdiv y hy

theorem exists_conjugate_of_harmonic_coordinate
    (g : RiemannianMetric 2 Plane) (D : LeviCivitaData g)
    {S : Set Plane} (hS : StarConvex ℝ 0 S)
    (hharmonic : ∀ x ∈ S, D.laplacian (fun y : Plane => y 0) x = 0) :
    ∃ V : Plane → ℝ, ContDiff ℝ ∞ V ∧ ∀ x ∈ S,
      HasFDerivAt V (rotatedFlux
        (fun y => g.pullbackVolumeDensity id y *
          WithLp.ofLp (D.gradient (fun z : Plane => z 0) y) 0)
        (fun y => g.pullbackVolumeDensity id y *
          WithLp.ofLp (D.gradient (fun z : Plane => z 0) y) 1)
        x) x := by
  have hf : ContDiff ℝ ∞ (fun y : Plane => y 0) :=
    (show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0).contDiff
  have hrho : ContDiff ℝ ∞ (g.pullbackVolumeDensity id) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (g.contDiffAt_pullbackVolumeDensity (f := id) contMDiffAt_id
      (by simpa using Function.injective_id)).1
  have hgrad : ContDiff ℝ ∞ (D.gradient (fun y : Plane => y 0)) :=
    contDiff_iff_contDiffAt.mpr fun _ => D.contDiffAt_gradient_euclidean hf.contDiffAt
  apply exists_conjugate_of_divergence_zero
    (hrho.mul ((show Plane →L[ℝ] ℝ from EuclideanSpace.proj 0).contDiff.comp hgrad))
    (hrho.mul ((show Plane →L[ℝ] ℝ from EuclideanSpace.proj 1).contDiff.comp hgrad)) hS
  intro x hx
  have h := D.density_mul_laplacian_eq_divergence hf.contDiffAt (x := x)
  simpa only [hharmonic x hx, mul_zero, Fin.sum_univ_two,
    Function.comp_def, EuclideanSpace.coe_proj] using! h.symm

end PoincareConjecture.M60

end
