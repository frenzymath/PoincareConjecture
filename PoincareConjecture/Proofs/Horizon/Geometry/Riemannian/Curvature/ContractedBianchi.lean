import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Derivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.RicciContraction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MetricTrace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.RicciDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Differential













set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture


lemma double_contraction_second_bianchi {ι E : Type*} [Fintype ι]
    (K : E → E → E → E → E → ℝ) (b : ι → E)
    (hfirst : ∀ u a b c d, K u a b c d = -K u b a c d)
    (hlast : ∀ u a b c d, K u a b c d = -K u a b d c)
    (hcyc : ∀ u a b c d, K u a b c d + K a b u c d + K b u a c d = 0)
    (v : E) :
    ∑ p, ∑ q, K (b p) v (b q) (b p) (b q) =
      (∑ p, ∑ q, K v (b p) (b q) (b p) (b q)) / 2 := by
  have hb (p q : ι) : K v (b p) (b q) (b p) (b q) -
      K (b p) v (b q) (b p) (b q) - K (b q) v (b p) (b q) (b p) = 0 := by
    have h := hcyc v (b p) (b q) (b p) (b q)
    rw [hfirst (b p) (b q) v (b p) (b q), hlast (b q) v (b p) (b p) (b q)] at h
    linarith
  have h := congrArg (fun f : ι → ι → ℝ => ∑ p, ∑ q, f p q)
    (funext fun p => funext fun q => hb p q)
  simp only [Finset.sum_sub_distrib, Finset.sum_const_zero] at h
  rw [Finset.sum_comm (f := fun p q => K (b q) v (b p) (b q) (b p))] at h
  linarith

end PoincareConjecture

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def frameRicciDerivative (D : LeviCivitaData g) (x : M)
    (i j k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) : ℝ :=
  D.covariantTensorDerivative D.ricciEvaluation x
    ![g.orthonormalBasis x i, g.orthonormalBasis x j, g.orthonormalBasis x k]

noncomputable def frameScalarDerivative (D : LeviCivitaData g) (x : M)
    (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) : ℝ :=
  mvfderiv (𝓡 n) (D.scalarCurvature) x (g.orthonormalBasis x i)


lemma covariantTensorDerivative_curvature_second_bianchi
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (u v w z q : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![u, v, w, z, q] +
      D.covariantTensorDerivative D.riemannEvaluation x ![v, w, u, z, q] +
      D.covariantTensorDerivative D.riemannEvaluation x ![w, u, v, z, q] = 0 := by
  rw [D.covariantTensorDerivative_riemannEvaluation_eq_inner_extend hD,
    D.covariantTensorDerivative_riemannEvaluation_eq_inner_extend hD,
    D.covariantTensorDerivative_riemannEvaluation_eq_inner_extend hD]
  exact D.second_bianchi_inner_on_fields_local z
    (FiberBundle.contMDiffAt_extend _ _ u)
    (FiberBundle.contMDiffAt_extend _ _ v)
    (FiberBundle.contMDiffAt_extend _ _ w)
    (FiberBundle.contMDiffAt_extend _ _ q)

lemma frameRicciDerivative_trace
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    ∑ p, frameRicciDerivative D x p i p =
      frameScalarDerivative D x i / 2 := by
  let b := g.orthonormalBasis x
  change (∑ p, D.covariantTensorDerivative D.ricciEvaluation x ![b p, b i, b p]) =
    mvfderiv (𝓡 n) D.scalarCurvature x (b i) / 2
  rw [← D.sum_covariantTensorDerivative_ricci_eq_scalar_derivative hD x (b i)]
  simp_rw [D.covariantTensorDerivative_ricciEvaluation_eq_sum_riemann hD]
  exact double_contraction_second_bianchi
    (fun u a b c d => D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d])
    b (D.covariantTensorDerivative_riemannEvaluation_skew_first hD x)
    (D.covariantTensorDerivative_riemannEvaluation_skew_last hD x)
    (D.covariantTensorDerivative_curvature_second_bianchi hD x) (b i)

lemma frameRicciDerivative_scalar_trace
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M)
    (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
    ∑ p, frameRicciDerivative D x i p p = frameScalarDerivative D x i := by
  exact D.sum_covariantTensorDerivative_ricci_eq_scalar_derivative hD x (g.orthonormalBasis x i)

end PoincareConjecture.LeviCivitaData

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : PoincareConjecture.RiemannianMetric n M}

theorem geometric_contraction_hypotheses
    (D : PoincareConjecture.LeviCivitaData g) (hD : D.CurvatureTensorCalculus) (x : M) :
    (∀ i, ∑ p, PoincareConjecture.LeviCivitaData.frameRicciDerivative D x p i p =
      PoincareConjecture.LeviCivitaData.frameScalarDerivative D x i / 2) ∧
    (∀ i, ∑ p, PoincareConjecture.LeviCivitaData.frameRicciDerivative D x i p p =
      PoincareConjecture.LeviCivitaData.frameScalarDerivative D x i) := by
  constructor
  · exact fun i => PoincareConjecture.LeviCivitaData.frameRicciDerivative_trace D hD x i
  · exact fun i => PoincareConjecture.LeviCivitaData.frameRicciDerivative_scalar_trace D hD x i

end Poincare.RicciFlow.Harnack
