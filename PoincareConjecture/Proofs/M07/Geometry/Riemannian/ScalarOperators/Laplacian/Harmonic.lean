import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.Dual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture

namespace LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

lemma laplacian_eq_sum_hessian_inverse (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) :
    D.laplacian f x = ∑ i, D.hessian f x
      (EuclideanSpace.basisFun (Fin n) ℝ i) ((g.inner x).inverse (EuclideanSpace.proj i)) := by
  have hfm : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x := contMDiffAt_iff_contDiffAt.mpr hf
  rw [D.laplacian_eq_sum_basis_connection_gradient hfm
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  apply Finset.sum_congr rfl
  intro i _
  rw [D.hessian_eq_inner_connection_gradient hfm, g.symm x]
  rw [(g.inner_isInvertible x).self_apply_inverse]
  rfl

lemma laplacian_eq_sum_fderiv_sub_christoffel (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) :
    D.laplacian f x =
      (∑ i, fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ((g.inner x).inverse (EuclideanSpace.proj i))) -
      fderiv ℝ f x (∑ i, CoordinateExponential.christoffelBilinear
        g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ i)
        ((g.inner x).inverse (EuclideanSpace.proj i))) := by
  rw [D.laplacian_eq_sum_hessian_inverse hf]
  simp_rw [D.hessian_eq_fderiv_sub_christoffel hf]
  rw [Finset.sum_sub_distrib, map_sum]

lemma sum_christoffel_inverse_eq_zero_of_harmonic (D : LeviCivitaData g)
    {x : EuclideanSpace ℝ (Fin n)}
    (hharm : ∀ i : Fin n, D.laplacian (fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x = 0) :
    (∑ i, CoordinateExponential.christoffelBilinear
      g.euclideanCoefficients x (EuclideanSpace.basisFun (Fin n) ℝ i)
      ((g.inner x).inverse (EuclideanSpace.proj i))) = 0 := by
  ext j
  have h := D.laplacian_eq_sum_fderiv_sub_christoffel
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt (n := ∞) (x := x))
  have hj : D.laplacian (EuclideanSpace.proj (𝕜 := ℝ) j) x = 0 := hharm j
  rw [hj] at h
  have hd : fderiv ℝ (EuclideanSpace.proj (𝕜 := ℝ) j) =
      fun _ : EuclideanSpace ℝ (Fin n) ↦ EuclideanSpace.proj j :=
    funext fun _ ↦ ContinuousLinearMap.fderiv _
  rw [hd] at h
  simpa using h

lemma laplacian_eq_sum_fderiv_of_harmonic (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x)
    (hharm : ∀ i : Fin n, D.laplacian (fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x = 0) :
    D.laplacian f x = ∑ i, ∑ j, g.inverseCoefficients x i j *
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  rw [D.laplacian_eq_sum_fderiv_sub_christoffel hf,
    D.sum_christoffel_inverse_eq_zero_of_harmonic hharm, map_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.basisFun (Fin n) ℝ i))
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr
      ((g.inner x).inverse (EuclideanSpace.proj i)))
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    RiemannianMetric.inverseCoefficients, PiLp.proj_apply] using h.symm

end LeviCivitaData
end PoincareConjecture
