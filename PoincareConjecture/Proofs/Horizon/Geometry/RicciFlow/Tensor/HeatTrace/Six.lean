import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.HeatTrace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.LaplacianTrace.Six


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {J : Set ℝ}

lemma LeviCivitaData.tensorTrace_ricciTensorAction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) {k : ℕ}
    (T : CovariantTensorEvaluation n M (k + 2)) (x : M)
    (v : Fin k → TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    g.tensorTrace (D.ricciTensorAction T) x v =
      D.ricciTensorAction (g.tensorTrace T) x v +
        2 * ∑ i, ∑ j, D.ricci x (b i) (b j) *
          T x (Fin.cons (b i) (Fin.cons (b j) v)) := by
  let b := g.orthonormalBasis x
  have hu {m : ℕ} (w : Fin m → TangentSpace (𝓡 n) x)
      (a c : TangentSpace (𝓡 n) x) (i : Fin m) :
      Function.update (Fin.cons (α := fun _ => TangentSpace (𝓡 n) x) a w) i.succ c =
        Fin.cons a (Function.update w i c) := by
    classical
    rw [← Fin.cons_update]
  have hexpand (a c : TangentSpace (𝓡 n) x) :
      D.ricciTensorAction T x (Fin.cons a (Fin.cons c v)) =
        (∑ j, D.ricci x a (b j) * T x (Fin.cons (b j) (Fin.cons c v))) +
        (∑ j, D.ricci x c (b j) * T x (Fin.cons a (Fin.cons (b j) v))) +
        ∑ l, ∑ j, D.ricci x (v l) (b j) *
          T x (Fin.cons a (Fin.cons c (Function.update v l (b j)))) := by
    simp only [LeviCivitaData.ricciTensorAction, Fin.sum_univ_succ,
      Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, hu]
    dsimp only [b]
    ring
  have hflip : (∑ i, ∑ j, D.ricci x (b i) (b j) *
      T x (Fin.cons (b j) (Fin.cons (b i) v))) =
      ∑ i, ∑ j, D.ricci x (b i) (b j) * T x (Fin.cons (b i) (Fin.cons (b j) v)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(hD.2.2.2.1 x (b j) (b i) (b i) (b j)).2.2.2]
  dsimp only
  change (∑ i, D.ricciTensorAction T x (Fin.cons (b i) (Fin.cons (b i) v))) = _
  simp only [hexpand, Finset.sum_add_distrib]
  rw [hflip]
  have htail : (∑ i, ∑ l, ∑ j, D.ricci x (v l) (b j) *
      T x (Fin.cons (b i) (Fin.cons (b i) (Function.update v l (b j))))) =
      D.ricciTensorAction (g.tensorTrace T) x v := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    rfl
  rw [htail]
  ring

lemma RicciFlow.tensorHeatOperator_tensorTrace_six
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {T W : ℝ → CovariantTensorEvaluation n M 6} {t : ℝ} (ht : t ∈ interior J)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hW : ∀ (y : M) (z : Fin 6 → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t)
    (x : M) (a b c d : TangentSpace (𝓡 n) x) :
    F.tensorHeatOperator (fun s => (F.metric s).tensorTrace (T s)) t x ![a, b, c, d] =
      (F.metric t).tensorTrace (F.tensorHeatOperator T t) x ![a, b, c, d] := by
  let D := F.connection t
  have hD := hC.tensor_calculus n M (F.metric t) D
  have htime := (F.hasDerivAt_tensorTrace ht x hT (hW x) ![a, b, c, d]).deriv
  have hlap := D.tensorLaplacian_tensorTrace_six (hT t) (hD.2.2.1 _ _ (hT t)) x a b c d
  have hact := D.tensorTrace_ricciTensorAction hD (T t) x ![a, b, c, d]
  have htrace : (F.metric t).tensorTrace (F.tensorHeatOperator T t) x ![a, b, c, d] =
      (F.metric t).tensorTrace (W t) x ![a, b, c, d] +
      (F.metric t).tensorTrace (D.ricciTensorAction (T t)) x ![a, b, c, d] -
      (F.metric t).tensorTrace (D.tensorLaplacian (T t)) x ![a, b, c, d] := by
    simp only [RiemannianMetric.tensorTrace, RicciFlow.tensorHeatOperator, (hW _ _).deriv,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rfl
  dsimp only at htime hact
  unfold RicciFlow.tensorHeatOperator
  rw [htime]
  change _ + D.ricciTensorAction ((F.metric t).tensorTrace (T t)) x ![a, b, c, d] -
    D.tensorLaplacian ((F.metric t).tensorTrace (T t)) x ![a, b, c, d] = _
  rw [hlap]
  change _ = (F.metric t).tensorTrace (F.tensorHeatOperator T t) x ![a, b, c, d]
  rw [htrace]
  linarith only [hact]

end PoincareConjecture
