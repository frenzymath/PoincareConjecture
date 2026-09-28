import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Product
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Reaction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.ProductDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Algebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma tensorTrace_tensorTrace_curvatureRicci
    (D : LeviCivitaData g) (x : M)
    (a b : TangentSpace (𝓡 n) x) :
    g.tensorTrace (g.tensorTrace (fun y z =>
      tensorProduct D.riemannEvaluation D.ricciEvaluation y
        (z ∘ (Equiv.ofBijective ![4, 0, 5, 2, 1, 3] (by decide))))) x ![a, b] =
      ∑ d, ∑ e, D.curvatureTensor x a (g.orthonormalBasis x d) b
        (g.orthonormalBasis x e) * D.ricci x (g.orthonormalBasis x d)
          (g.orthonormalBasis x e) := by
  let σ : Equiv.Perm (Fin 6) :=
    Equiv.ofBijective ![4, 0, 5, 2, 1, 3] (by decide)
  simp only [RiemannianMetric.tensorTrace]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hz :
      (Fin.cons (g.orthonormalBasis x d)
        (Fin.cons (g.orthonormalBasis x d)
          (Fin.cons (g.orthonormalBasis x e)
            (Fin.cons (g.orthonormalBasis x e) ![a, b]))) :
          Fin 6 → TangentSpace (𝓡 n) x) ∘ σ =
        ![a, g.orthonormalBasis x d, b, g.orthonormalBasis x e,
          g.orthonormalBasis x d, g.orthonormalBasis x e] := by
    ext i
    fin_cases i <;> rfl
  change tensorProduct D.riemannEvaluation D.ricciEvaluation x
      ((Fin.cons (g.orthonormalBasis x d)
        (Fin.cons (g.orthonormalBasis x d)
          (Fin.cons (g.orthonormalBasis x e)
            (Fin.cons (g.orthonormalBasis x e) ![a, b]))) :
        Fin 6 → TangentSpace (𝓡 n) x) ∘ σ) = _
  rw [hz]
  simp only [tensorProduct]
  unfold riemannEvaluation ricciEvaluation
  rfl

lemma curvatureRicci_eq_double_trace (D : LeviCivitaData g) :
    (fun y (z : Fin 2 → TangentSpace (𝓡 n) y) =>
      ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 1)
        (g.orthonormalBasis y j) * D.ricci y (g.orthonormalBasis y i)
          (g.orthonormalBasis y j)) =
    g.tensorTrace (g.tensorTrace (fun y z =>
      tensorProduct D.riemannEvaluation D.ricciEvaluation y
        (z ∘ (Equiv.ofBijective ![4, 0, 5, 2, 1, 3] (by decide))))) := by
  funext x z
  have hz : ![z 0, z 1] = z := by ext i; fin_cases i <;> rfl
  simpa only [hz] using (D.tensorTrace_tensorTrace_curvatureRicci x (z 0) (z 1)).symm

lemma covariantTensorDerivative_curvatureRicci
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a b c : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y z =>
      ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 1)
        (g.orthonormalBasis y j) * D.ricci y (g.orthonormalBasis y i)
          (g.orthonormalBasis y j)) x ![a, b, c] =
    ∑ i, ∑ j, (D.covariantTensorDerivative D.riemannEvaluation x
      ![a, b, g.orthonormalBasis x i, c, g.orthonormalBasis x j] *
        D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j) +
      D.curvatureTensor x b (g.orthonormalBasis x i) c (g.orthonormalBasis x j) *
        D.covariantTensorDerivative D.ricciEvaluation x
          ![a, g.orthonormalBasis x i, g.orthonormalBasis x j]) := by
  let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective ![4, 0, 5, 2, 1, 3] (by decide)
  let S := fun y z => tensorProduct D.riemannEvaluation D.ricciEvaluation y (z ∘ σ)
  have hS : IsSmoothCovariantTensor S :=
    (isSmoothCovariantTensor_tensorProduct hD.1 hD.2.1).perm σ
  rw [D.curvatureRicci_eq_double_trace]
  have ht := D.covariantTensorDerivative_tensorTrace (hS.tensorTrace (g := g)) x a ![b, c]
  simp only [Matrix.Fin.cons_vecCons] at ht
  rw [ht]
  have ht' (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :=
    D.covariantTensorDerivative_tensorTrace hS x a
      ![g.orthonormalBasis x i, g.orthonormalBasis x i, b, c]
  simp only [Matrix.Fin.cons_vecCons] at ht'
  simp_rw [ht']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change D.covariantTensorDerivative S x
    ![a, g.orthonormalBasis x i, g.orthonormalBasis x i,
      g.orthonormalBasis x j, g.orthonormalBasis x j, b, c] = _
  dsimp only [S]
  rw [D.covariantTensorDerivative_reindex]
  have hz : Fin.cons a (fun q : Fin 6 =>
      ![a, g.orthonormalBasis x i, g.orthonormalBasis x i,
        g.orthonormalBasis x j, g.orthonormalBasis x j, b, c] (σ q).succ) =
      ![a, b, g.orthonormalBasis x i, c, g.orthonormalBasis x j,
        g.orthonormalBasis x i, g.orthonormalBasis x j] := by
    ext q
    fin_cases q <;> rfl
  change D.covariantTensorDerivative (tensorProduct D.riemannEvaluation D.ricciEvaluation) x
    (Fin.cons a (fun q : Fin 6 =>
      ![a, g.orthonormalBasis x i, g.orthonormalBasis x i,
        g.orthonormalBasis x j, g.orthonormalBasis x j, b, c] (σ q).succ)) = _
  rw [hz]
  have hp := D.covariantTensorDerivative_tensorProduct hD.1 hD.2.1 x a
    ![b, g.orthonormalBasis x i, c, g.orthonormalBasis x j,
      g.orthonormalBasis x i, g.orthonormalBasis x j]
  simp only [Matrix.Fin.cons_vecCons] at hp
  rw [hp]
  have hv₁ : (fun q : Fin 4 =>
      ![b, g.orthonormalBasis x i, c, g.orthonormalBasis x j,
        g.orthonormalBasis x i, g.orthonormalBasis x j] (Fin.castAdd 2 q)) =
      ![b, g.orthonormalBasis x i, c, g.orthonormalBasis x j] := by
    ext q
    fin_cases q <;> rfl
  have hv₂ : (fun q : Fin 2 =>
      ![b, g.orthonormalBasis x i, c, g.orthonormalBasis x j,
        g.orthonormalBasis x i, g.orthonormalBasis x j] (Fin.natAdd 4 q)) =
      ![g.orthonormalBasis x i, g.orthonormalBasis x j] := by
    ext q
    fin_cases q <;> rfl
  rw [hv₁, hv₂]
  rfl

lemma isSmoothCovariantTensor_curvatureRicci
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) :
    IsSmoothCovariantTensor (fun y (z : Fin 2 → TangentSpace (𝓡 n) y) =>
      ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 1)
        (g.orthonormalBasis y j) * D.ricci y (g.orthonormalBasis y i)
          (g.orthonormalBasis y j)) := by
  rw [D.curvatureRicci_eq_double_trace]
  exact ((isSmoothCovariantTensor_tensorProduct hD.1 hD.2.1).perm _).tensorTrace.tensorTrace

lemma isSmoothCovariantTensor_ricciReaction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) :
    IsSmoothCovariantTensor (fun y (z : Fin 2 → TangentSpace (𝓡 n) y) =>
      D.ricciReaction y (z 0) (z 1)) := by
  exact ((D.isSmoothCovariantTensor_curvatureRicci hD).const_mul 2).sub
    ((D.isSmoothCovariantTensor_tensorProduct_trace_order_two hD.2.1 hD.2.1).const_mul 2)

lemma covariantTensorDerivative_ricciReaction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a b c : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    D.covariantTensorDerivative (fun y z => D.ricciReaction y (z 0) (z 1)) x ![a, b, c] =
      2 * (∑ i, ∑ j, (D.covariantTensorDerivative D.riemannEvaluation x ![a, b, e i, c, e j] *
        D.ricci x (e i) (e j) + D.curvatureTensor x b (e i) c (e j) *
          D.covariantTensorDerivative D.ricciEvaluation x ![a, e i, e j])) -
      2 * (∑ i, (D.covariantTensorDerivative D.ricciEvaluation x ![a, b, e i] *
        D.ricci x (e i) c + D.ricci x b (e i) *
          D.covariantTensorDerivative D.ricciEvaluation x ![a, e i, c])) := by
  have hC := D.isSmoothCovariantTensor_curvatureRicci hD
  have hQ := D.isSmoothCovariantTensor_tensorProduct_trace_order_two hD.2.1 hD.2.1
  change D.covariantTensorDerivative (fun y z =>
      2 * (∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 1)
        (g.orthonormalBasis y j) * D.ricci y (g.orthonormalBasis y i) (g.orthonormalBasis y j)) -
      2 * (∑ i, D.ricciEvaluation y ![z 0, g.orthonormalBasis y i] *
        D.ricciEvaluation y ![g.orthonormalBasis y i, z 1])) x ![a, b, c] = _
  rw [D.covariantTensorDerivative_sub (hC.const_mul 2) (hQ.const_mul 2)]
  dsimp only
  rw [D.covariantTensorDerivative_const_mul hC, D.covariantTensorDerivative_const_mul hQ]
  dsimp only
  rw [D.covariantTensorDerivative_curvatureRicci hD,
    D.covariantTensorDerivative_tensorProduct_trace_order_two hD.2.1 hD.2.1]
  rfl

end PoincareConjecture.LeviCivitaData
