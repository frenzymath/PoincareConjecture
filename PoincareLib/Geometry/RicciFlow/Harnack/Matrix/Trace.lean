import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.Riemannian.Tensor.LaplacianTrace
import PoincareLib.Geometry.Riemannian.Curvature.ContractedBianchi

/-!
# Geometric trace of Hamilton's Harnack tensors

The retained Levi-Civita connection supplies both differential contractions:
the trace of the rough Ricci Laplacian and contracted second Bianchi.
Consequently the trace of Hamilton's tensors is the scalar Harnack expression,
with its time derivative supplied by the original curvature theory.

See Kleiner-Lott, Appendix F, pp. 2850-2851, and Chow et al., Part II,
Corollary 15.3, equation (15.18), pp. 263-264 (PDF pp. 290-291).
Positivity of the matrix expression remains a separate geometric obligation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Contracted second Bianchi gives the trace of Hamilton's three-tensor on
an arbitrary tangent vector. -/
lemma hamiltonP_trace (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    (∑ i, hamiltonP D x v (g.orthonormalBasis x i) (g.orthonormalBasis x i)) =
      mvfderiv (𝓡 n) D.scalarCurvature x v / 2 := by
  let b := g.orthonormalBasis x
  have hdiv : (∑ i, D.covariantTensorDerivative D.ricciEvaluation x ![b i, v, b i]) =
      mvfderiv (𝓡 n) D.scalarCurvature x v / 2 := by
    rw [← D.sum_covariantTensorDerivative_ricci_eq_scalar_derivative hD x v]
    simp_rw [D.covariantTensorDerivative_ricciEvaluation_eq_sum_riemann hD]
    exact double_contraction_second_bianchi
      (fun u a b c d => D.covariantTensorDerivative D.riemannEvaluation x ![u, a, b, c, d])
      b (D.covariantTensorDerivative_riemannEvaluation_skew_first hD x)
      (D.covariantTensorDerivative_riemannEvaluation_skew_last hD x)
      (D.covariantTensorDerivative_curvature_second_bianchi hD x) v
  simp only [hamiltonP, Finset.sum_sub_distrib]
  rw [D.sum_covariantTensorDerivative_ricci_eq_scalar_derivative hD x v, hdiv]
  ring

/-- The geometric two-tensor trace has its scalar Laplacian and squared Ricci
norm, with no unproved contraction hypotheses. -/
lemma hamiltonM_trace (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (τ : ℝ) (x : M) :
    (∑ i, hamiltonM D τ x (g.orthonormalBasis x i) (g.orthonormalBasis x i)) =
      D.laplacian D.scalarCurvature x / 2 + D.ricciNormSq x +
        D.scalarCurvature x / (2 * τ) := by
  let b := g.orthonormalBasis x
  exact harnackTwoTensor_trace
    (fun i j k l => D.curvatureTensor x (b i) (b j) (b k) (b l))
    (fun i j => D.ricci x (b i) (b j))
    (fun i j => D.tensorLaplacian D.ricciEvaluation x ![b i, b j])
    (fun i j => D.hessian D.scalarCurvature x (b i) (b j))
    (D.laplacian D.scalarCurvature x) τ (fun _ _ => rfl)
    (fun i j => (hD.2.2.2.1 x (b i) (b j) (b i) (b j)).2.2.2)
    (D.sum_tensorLaplacian_ricci_eq_laplacian_scalar hD x) rfl

/-- Twice the geometric matrix trace is the scalar Harnack expression with
the scalar evolution value in its time-derivative slot. -/
lemma hamilton_trace_eq (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (τ : ℝ) (x : M) (v : TangentSpace (𝓡 n) x) :
    2 * (∑ i, (hamiltonM D τ x (g.orthonormalBasis x i) (g.orthonormalBasis x i) +
      2 * hamiltonP D x v (g.orthonormalBasis x i) (g.orthonormalBasis x i) +
      D.curvatureTensor x v (g.orthonormalBasis x i) v (g.orthonormalBasis x i))) =
      (D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x) +
        D.scalarCurvature x / τ + 2 * mvfderiv (𝓡 n) D.scalarCurvature x v +
        2 * D.ricci x v v := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hamiltonM_trace D hD, hamiltonP_trace D hD]
  change 2 * (D.laplacian D.scalarCurvature x / 2 + D.ricciNormSq x +
    D.scalarCurvature x / (2 * τ) +
    2 * (mvfderiv (𝓡 n) D.scalarCurvature x v / 2) + D.ricci x v v) = _
  ring

/-- The exact differential expression in finite Harnack is twice the
geometric matrix trace, for a derivative obtained from the frozen M04 theory. -/
theorem scalar_harnack_eq_hamilton_trace
    (hC : RicciFlowCurvatureCalculus.{u}) (T₀ T₁ : ℝ)
    (F : RicciFlow n M (Set.Ioo T₀ T₁)) (t : ℝ) (ht : t ∈ Set.Ioo T₀ T₁)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    ∃ dR : ℝ,
      HasDerivWithinAt (fun s => (F.connection s).scalarCurvature x) dR
        (Set.Ioo T₀ T₁) t ∧
      dR + (F.connection t).scalarCurvature x / (t - T₀) +
        2 * mvfderiv (𝓡 n) (F.connection t).scalarCurvature x v +
        2 * (F.connection t).ricci x v v =
      2 * (∑ i, (hamiltonM (F.connection t) (t - T₀) x
          ((F.metric t).orthonormalBasis x i) ((F.metric t).orthonormalBasis x i) +
        2 * hamiltonP (F.connection t) x v
          ((F.metric t).orthonormalBasis x i) ((F.metric t).orthonormalBasis x i) +
        (F.connection t).curvatureTensor x v ((F.metric t).orthonormalBasis x i)
          v ((F.metric t).orthonormalBasis x i))) := by
  refine ⟨_, hC.scalar_evolution n M (Set.Ioo T₀ T₁) F t ht x, ?_⟩
  exact (hamilton_trace_eq (F.connection t)
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) (t - T₀) x v).symm

/-! The trace identity is the final algebraic adapter in the finite producer:
pointwise nonnegativity of Hamilton's diagonal quadratic immediately yields
the exact scalar differential inequality required by the frozen M06 field. -/
theorem finite_differential_of_hamilton_diagonal_nonneg
    (hC : RicciFlowCurvatureCalculus.{u}) (T₀ T₁ : ℝ)
    (F : RicciFlow n M (Set.Ioo T₀ T₁)) (t : ℝ)
    (ht : t ∈ Set.Ioo T₀ T₁) (x : M)
    (v : TangentSpace (𝓡 n) x)
    (hpos : ∀ i,
      0 ≤ (hamiltonM (F.connection t) (t - T₀) x
          ((F.metric t).orthonormalBasis x i)
          ((F.metric t).orthonormalBasis x i) +
        2 * hamiltonP (F.connection t) x v
          ((F.metric t).orthonormalBasis x i)
          ((F.metric t).orthonormalBasis x i) +
        (F.connection t).curvatureTensor x v
          ((F.metric t).orthonormalBasis x i) v
          ((F.metric t).orthonormalBasis x i)) ) :
    ∃ dR : ℝ,
      HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) dR
        (Set.Ioo T₀ T₁) t ∧
      0 ≤ dR + (F.connection t).scalarCurvature x / (t - T₀) +
        2 * mvfderiv (𝓡 n) (F.connection t).scalarCurvature x v +
        2 * (F.connection t).ricci x v v := by
  obtain ⟨dR, hdR, htrace⟩ := scalar_harnack_eq_hamilton_trace
    hC T₀ T₁ F t ht x v
  refine ⟨dR, hdR, ?_⟩
  rw [htrace]
  have hsum : 0 ≤ ∑ i,
      (hamiltonM (F.connection t) (t - T₀) x
          ((F.metric t).orthonormalBasis x i)
          ((F.metric t).orthonormalBasis x i) +
        2 * hamiltonP (F.connection t) x v
          ((F.metric t).orthonormalBasis x i)
          ((F.metric t).orthonormalBasis x i) +
        (F.connection t).curvatureTensor x v
          ((F.metric t).orthonormalBasis x i) v
          ((F.metric t).orthonormalBasis x i)) :=
    Finset.sum_nonneg (fun i _ ↦ hpos i)
  exact mul_nonneg (by norm_num) hsum

end Poincare.RicciFlow.Harnack
