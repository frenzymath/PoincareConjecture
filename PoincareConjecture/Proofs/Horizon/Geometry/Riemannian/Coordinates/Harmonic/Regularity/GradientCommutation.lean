import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Derivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Commutation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureSymmetry

noncomputable section
set_option autoImplicit false

open Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem sum_covariantTensorDerivative_hessian_apply (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (z : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x
      ![g.orthonormalBasis x i, g.orthonormalBasis x i, z]) =
      mvfderiv (𝓡 n) (D.laplacian f) x z + D.ricci x (D.gradient f x) z := by
  have hterm (i) :
      D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x
        ![g.orthonormalBasis x i, g.orthonormalBasis x i, z] =
      D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x
        ![z, g.orthonormalBasis x i, g.orthonormalBasis x i] +
      D.curvatureTensor x z (g.orthonormalBasis x i)
        (D.gradient f x) (g.orthonormalBasis x i) := by
    rw [D.covariantTensorDerivative_hessian_symm hf]
    have h := D.covariantTensorDerivative_hessian_commutator hf x
      (g.orthonormalBasis x i) z (g.orthonormalBasis x i)
    rw [← D.inner_gradient, g.symm] at h
    change _ = -D.curvatureTensor x (g.orthonormalBasis x i) z
      (D.gradient f x) (g.orthonormalBasis x i) at h
    rw [D.curvatureTensor_swap_first, neg_neg] at h
    simpa only [add_comm] using (sub_eq_iff_eq_add).mp h
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, D.sum_covariantTensorDerivative_hessian_eq hf]
  congr 1
  unfold ricci
  apply Finset.sum_congr rfl
  intro i _
  change g.inner x (D.curvature x z (g.orthonormalBasis x i) (g.orthonormalBasis x i))
    (D.gradient f x) = g.inner x
      (D.curvature x (D.gradient f x) (g.orthonormalBasis x i) (g.orthonormalBasis x i)) z
  simpa only [radialCurvature_apply, g.symm x z] using
    D.inner_radialCurvature_symm x (g.orthonormalBasis x i) z (D.gradient f x)

theorem sum_inner_second_connection_gradient (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (z : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    (∑ i, g.inner x
      (D.connection (D.covariantDerivativeOnFields (E i) (D.gradient f)) x (b i) -
        D.connection (D.gradient f) x (D.connection (E i) x (b i))) z) =
      g.inner x (D.gradient (D.laplacian f) x) z + D.ricci x (D.gradient f x) z := by
  dsimp only
  rw [D.inner_gradient]
  simpa only [D.covariantTensorDerivative_hessian_eq hf] using
    D.sum_covariantTensorDerivative_hessian_apply hf x z

theorem sum_inner_second_connection_harmonic_gradient (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (hharm : D.laplacian f =ᶠ[𝓝 x] fun _ => 0)
    (z : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    (∑ i, g.inner x
      (D.connection (D.covariantDerivativeOnFields (E i) (D.gradient f)) x (b i) -
        D.connection (D.gradient f) x (D.connection (E i) x (b i))) z) =
      D.ricci x (D.gradient f x) z := by
  dsimp only
  rw [D.sum_inner_second_connection_gradient hf x z, D.inner_gradient,
    Poincare.mvfderiv_eq_of_eventuallyEq hharm, mvfderiv_const, zero_apply, zero_add]

end PoincareConjecture.LeviCivitaData
