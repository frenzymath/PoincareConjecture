import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatGradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeDerivative.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.LaplacianTrace.Four







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {J : Set ℝ}

lemma LeviCivitaData.tensorTrace_ricciTensorAction_four
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (T : CovariantTensorEvaluation n M 4) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    g.tensorTrace (D.ricciTensorAction T) x ![u, v] =
      D.ricciTensorAction (g.tensorTrace T) x ![u, v] +
        2 * ∑ i, ∑ j, D.ricci x (b i) (b j) * T x ![b i, b j, u, v] := by
  let b := g.orthonormalBasis x
  have hexpand (a c d e : TangentSpace (𝓡 n) x) :
      D.ricciTensorAction T x ![a, c, d, e] =
        (∑ j, D.ricci x a (b j) * T x ![b j, c, d, e]) +
        (∑ j, D.ricci x c (b j) * T x ![a, b j, d, e]) +
        (∑ j, D.ricci x d (b j) * T x ![a, c, b j, e]) +
        (∑ j, D.ricci x e (b j) * T x ![a, c, d, b j]) := by
    have hu (w : TangentSpace (𝓡 n) x) :
        Function.update ![a, c, d, e] 0 w = ![w, c, d, e] ∧
        Function.update ![a, c, d, e] 1 w = ![a, w, d, e] ∧
        Function.update ![a, c, d, e] 2 w = ![a, c, w, e] ∧
        Function.update ![a, c, d, e] 3 w = ![a, c, d, w] := by
      constructor
      · ext i; fin_cases i <;> simp
      constructor
      · ext i; fin_cases i <;> simp
      constructor <;> (ext i; fin_cases i <;> simp)
    unfold LeviCivitaData.ricciTensorAction
    rw [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, hu]
    rfl
  have hflip : (∑ i, ∑ j, D.ricci x (b i) (b j) * T x ![b j, b i, u, v]) =
      ∑ i, ∑ j, D.ricci x (b i) (b j) * T x ![b i, b j, u, v] := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(hD.2.2.2.1 x (b j) (b i) u v).2.2.2]
  dsimp only
  change (∑ i, D.ricciTensorAction T x ![b i, b i, u, v]) = _
  simp only [hexpand, Finset.sum_add_distrib]
  rw [D.ricciTensorAction_two]
  simp only [RiemannianMetric.tensorTrace, Matrix.Fin.cons_vecCons,
    Finset.mul_sum, Finset.sum_add_distrib]
  dsimp only [b] at hflip ⊢
  rw [hflip]
  have hleft : (∑ i, ∑ j, D.ricci x u (b j) * T x ![b i, b i, b j, v]) =
      ∑ j, ∑ i, D.ricci x u (b j) * T x ![b i, b i, b j, v] := Finset.sum_comm
  have hright : (∑ i, ∑ j, D.ricci x v (b j) * T x ![b i, b i, u, b j]) =
      ∑ j, ∑ i, D.ricci x v (b j) * T x ![b i, b i, u, b j] := Finset.sum_comm
  dsimp only [b] at hleft hright
  rw [hleft, hright]
  simp only [← Finset.mul_sum]
  ring

lemma RicciFlow.tensorHeatOperator_tensorTrace_four
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {T W : ℝ → CovariantTensorEvaluation n M 4} {t : ℝ} (ht : t ∈ interior J)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hW : ∀ (y : M) (z : Fin 4 → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    F.tensorHeatOperator (fun s => (F.metric s).tensorTrace (T s)) t x ![u, v] =
      (F.metric t).tensorTrace (F.tensorHeatOperator T t) x ![u, v] := by
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  have hD := hC.tensor_calculus n M (F.metric t) D
  have htime := (F.hasDerivAt_tensorTrace ht x hT (hW x) ![u, v]).deriv
  have hlap := D.tensorLaplacian_tensorTrace_four (hT t) (hD.2.2.1 _ _ (hT t)) x u v
  have hact := D.tensorTrace_ricciTensorAction_four hD (T t) x u v
  have htrace : (F.metric t).tensorTrace (F.tensorHeatOperator T t) x ![u, v] =
      (F.metric t).tensorTrace (W t) x ![u, v] +
      (F.metric t).tensorTrace (D.ricciTensorAction (T t)) x ![u, v] -
      (F.metric t).tensorTrace (D.tensorLaplacian (T t)) x ![u, v] := by
    simp only [RiemannianMetric.tensorTrace, RicciFlow.tensorHeatOperator, (hW _ _).deriv,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rfl
  dsimp only at htime hact
  simp only [Matrix.Fin.cons_vecCons] at htime
  unfold RicciFlow.tensorHeatOperator
  rw [htime]
  change _ + D.ricciTensorAction ((F.metric t).tensorTrace (T t)) x ![u, v] -
    D.tensorLaplacian ((F.metric t).tensorTrace (T t)) x ![u, v] = _
  rw [hlap]
  change _ = (F.metric t).tensorTrace (F.tensorHeatOperator T t) x ![u, v]
  rw [htrace]
  linarith only [hact]

end PoincareConjecture
