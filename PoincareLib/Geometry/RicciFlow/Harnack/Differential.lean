import PoincareLib.Geometry.RicciFlow.Harnack.TensorContractions
import PoincareLib.Geometry.RicciFlow.Curvature.Reaction
import PoincareLib.Geometry.Riemannian.Tensor.RicciDerivative
import PoincareLib.Geometry.RicciFlow.Harnack.Matrix.Tensors
import PoincareLib.Geometry.RicciFlow.Harnack.Matrix.Derivatives
import PoincareLib.Geometry.RicciFlow.Harnack.Matrix.TimeCorrection
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The trace expression in the differential Harnack estimate

The finite orthonormal trace calculation is equation (15.18) in Chow et al.,
Part II, Corollary 15.3 (PDF pages 290-291), equivalently Kleiner-Lott,
Appendix F, pp. 2850-2851. Curvature slots agree with the frozen convention
`Ric i j = ∑ a, Rm i a j a`.

This module does not yet prove the finite differential Harnack inequality.
The remaining geometric producers are contracted Bianchi, compatibility of
the displayed contractions with covariant derivatives, Hamilton's matrix
evolution and its noncompact maximum principle, and the componentwise
upgrade of per-slice curvature bounds to compact-time bounds. In particular,
no positivity assumption or certificate for the desired estimate is added.
-/

open scoped Manifold ContDiff Bundle BigOperators
open PoincareMT

namespace Poincare.RicciFlow.Harnack

variable {I : Type*} [Fintype I]

/-- The orthonormal trace of the matrix Harnack expression is the scalar
Harnack expression. The scalar time derivative is represented by its
evolution value `lapR + 2 * ∑ i, ∑ j, (Ric i j) ^ 2`. -/
lemma traceHarnackExpression_eq (Rm : I → I → I → I → ℝ)
    (Ric LapRic HessR : I → I → ℝ) (A : I → I → I → ℝ)
    (dR V : I → ℝ) (lapR τ : ℝ)
    (hRic : ∀ i j, ∑ a, Rm i a j a = Ric i j)
    (hsymm : ∀ i j, Ric i j = Ric j i)
    (hLap : ∑ i, LapRic i i = lapR) (hHess : ∑ i, HessR i i = lapR)
    (hdiv : ∀ i, ∑ p, A p i p = dR i / 2)
    (htrace : ∀ i, ∑ p, A i p p = dR i) :
    2 * (∑ i, (LapRic i i - HessR i i / 2 +
      (2 * (∑ k, ∑ l, Rm k i l i * Ric k l) -
        ∑ k, Ric i k * Ric k i) + Ric i i / (2 * τ))) -
      2 * (2 * (∑ i, (∑ p, (A p i p - A i p p)) * V i)) +
      2 * (∑ i, ∑ j, (∑ a, Rm i a j a) * V i * V j) =
    (lapR + 2 * (∑ i, ∑ j, (Ric i j) ^ 2)) + (∑ i, Ric i i) / τ +
      2 * (∑ i, dR i * V i) + 2 * (∑ i, ∑ j, Ric i j * V i * V j) := by
  rw [harnackTwoTensor_trace Rm Ric LapRic HessR lapR τ hRic hsymm hLap hHess,
    ricciDerivative_trace_pairing A dR V hdiv htrace]
  simp_rw [hRic]
  ring

/- Hamilton's reaction block is the squared Ricci norm after tracing, hence
   it is nonnegative independently of the differential and barrier terms. -/
lemma harnackReaction_trace_nonneg (Rm : I → I → I → I → ℝ)
    (Ric : I → I → ℝ)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l)
    (hsymm : ∀ i k, Ric i k = Ric k i) :
    0 ≤ ∑ i, (2 * (∑ k, ∑ l, Rm k i l i * Ric k l) -
      ∑ k, Ric i k * Ric k i) := by
  rw [harnackReaction_trace Rm Ric hRic hsymm]
  exact Finset.sum_nonneg fun i hi ↦
    Finset.sum_nonneg fun k hk ↦ sq_nonneg (Ric i k)

/- The frozen Ricci definition and curvature symmetries provide the frame
   contraction and symmetry hypotheses consumed by the finite trace algebra. -/
lemma frameRicci_contraction_and_symmetry
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : PoincareMT.RiemannianMetric n M)
    (D : PoincareMT.LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    let b := g.orthonormalBasis x
    (∀ i j, ∑ a, D.curvatureTensor x (b i) (b a) (b j) (b a) =
      D.ricci x (b i) (b j)) ∧
    (∀ i j, D.ricci x (b i) (b j) = D.ricci x (b j) (b i)) := by
  let b := g.orthonormalBasis x
  constructor
  · intro i j
    rfl
  · intro i j
    exact (hD.2.2.2.1 x (b i) (b j) (b i) (b j)).2.2.2

lemma frameRicciDerivative_last_symm
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : PoincareMT.RiemannianMetric n M)
    (D : PoincareMT.LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    let b := g.orthonormalBasis x
    ∀ (i j k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))),
      D.covariantTensorDerivative D.ricciEvaluation x ![b i, b j, b k] =
        D.covariantTensorDerivative D.ricciEvaluation x ![b i, b k, b j] := by
  dsimp
  intro i j k
  simpa using
    (PoincareMT.LeviCivitaData.covariantTensorDerivative_ricciEvaluation_symm
      D hD x (g.orthonormalBasis x i) (g.orthonormalBasis x j)
        (g.orthonormalBasis x k))

lemma ricciReaction_trace_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : PoincareMT.RiemannianMetric n M)
    (D : PoincareMT.LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M) :
    let b := g.orthonormalBasis x
    ∑ a, D.ricciReaction x (b a) (b a) = 0 := by
  let b := g.orthonormalBasis x
  have hs := hD.2.2.2.1
  have hfirst (u v w z : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x u v w z = -D.curvatureTensor x v u w z := by
    rw [(hs x u v w z).2.1, (hs x w z u v).1, (hs x w z v u).2.1]
  have hslots (a i j) : D.curvatureTensor x (b a) (b i) (b a) (b j) =
      D.curvatureTensor x (b i) (b a) (b j) (b a) := by
    rw [hfirst, (hs x (b i) (b a) (b a) (b j)).1, neg_neg]
  change (∑ a, (2 * (∑ i, ∑ j,
    D.curvatureTensor x (b a) (b i) (b a) (b j) * D.ricci x (b i) (b j)) -
    2 * (∑ i, D.ricci x (b a) (b i) * D.ricci x (b i) (b a)))) = 0
  have hcontract (i j) : (∑ a, D.curvatureTensor x (b a) (b i) (b a) (b j)) =
      D.ricci x (b i) (b j) := by
    change (∑ a, D.curvatureTensor x (b a) (b i) (b a) (b j)) =
      ∑ a, D.curvatureTensor x (b i) (b a) (b j) (b a)
    exact Finset.sum_congr rfl (fun a _ ↦ hslots a i j)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    curvatureRicci_trace (fun i j k l ↦ D.curvatureTensor x (b j) (b i) (b l) (b k))
      (fun i j ↦ D.ricci x (b i) (b j)) hcontract,
    ricciSquare_trace (fun i j ↦ D.ricci x (b i) (b j))
      (fun i j ↦ (hs x (b i) (b j) (b i) (b j)).2.2.2)]
  ring

end Poincare.RicciFlow.Harnack
