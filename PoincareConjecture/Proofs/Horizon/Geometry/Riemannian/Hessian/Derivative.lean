import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Symmetry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MetricTrace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Symmetry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem covariantTensorDerivative_hessian_eq (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x ![a, b, c] =
      g.inner x
        (D.connection (D.covariantDerivativeOnFields
            (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b) (D.gradient f)) x a -
          D.connection (D.gradient f) x
            (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b) x a)) c := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b
  let Z := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) c
  have hY := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) b
  have hZ := FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞) c
  have hW := D.contMDiffAt_covariantDerivativeOnFields hY (D.contMDiff_gradient hf x)
  have hd := D.horizon_mvfderiv_inner X (hW.mdifferentiableAt (by simp))
    (hZ.mdifferentiableAt (by simp))
  simp only [covariantDerivativeOnFields, X, FiberBundle.extend_apply_self] at hd
  simp only [covariantTensorDerivative, Fin.sum_univ_two, Matrix.cons_val_zero]
  simp_rw [D.hessian_eq_inner_connection_gradient (hf _)]
  change mvfderiv (𝓡 n)
      (fun y => g.inner y (D.connection (D.gradient f) y (Y y)) (Z y)) x a -
      (g.inner x (D.connection (D.gradient f) x (D.connection Y x a)) c +
        g.inner x (D.connection (D.gradient f) x b) (D.connection Z x a)) = _
  rw [hd]
  simp only [map_sub, sub_apply, Y]
  ring

theorem covariantTensorDerivative_hessian_symm (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x ![a, b, c] =
      D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x ![a, c, b] := by
  let T : CovariantTensorEvaluation n M 2 := fun y v => D.hessian f y (v 0) (v 1)
  have hT (y : M) (v : Fin 2 → TangentSpace (𝓡 n) y) :
      T y (v ∘ Equiv.swap 0 1) = T y v := by
    simpa [T] using D.hessian_symm hf y (v 1) (v 0)
  have h := D.covariantTensorDerivative_perm T (Equiv.swap 0 1) hT x a ![b, c]
  have hv : ![b, c] ∘ Equiv.swap 0 1 = ![c, b] := by
    ext i
    fin_cases i <;> simp
  rw [hv] at h
  exact h.symm

theorem sum_covariantTensorDerivative_hessian_eq (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (a : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative (fun y v => D.hessian f y (v 0) (v 1)) x
      ![a, g.orthonormalBasis x i, g.orthonormalBasis x i]) =
        mvfderiv (𝓡 n) (D.laplacian f) x a := by
  exact D.sum_covariantTensorDerivative_eq_mvfderiv_metricTrace
    (D.hessian_isSmoothCovariantTensor hf) x a

end PoincareConjecture.LeviCivitaData
