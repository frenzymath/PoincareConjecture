import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Commutation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Algebra









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


lemma covariantTensorDerivative_tensorLaplacian_commutator_all_raw
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    {k : ℕ} {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (a : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    let S : CovariantTensorEvaluation n M (k + 2) := fun y z =>
      D.covariantCurvatureAction T y (z 0) (z 1) (fun i => z i.succ.succ)
    D.covariantTensorDerivative (D.tensorLaplacian T) x (Fin.cons a v) -
        D.tensorLaplacian (D.covariantTensorDerivative T) x (Fin.cons a v) =
      -∑ i, (D.covariantCurvatureAction (D.covariantTensorDerivative T) x a (b i)
          (Fin.cons (b i) v) +
        D.covariantTensorDerivative S x (Fin.cons (b i) (Fin.cons a (Fin.cons (b i) v)))) := by
  let S : CovariantTensorEvaluation n M (k + 2) := fun y z =>
    D.covariantCurvatureAction T y (z 0) (z 1) (fun i => z i.succ.succ)
  let A := D.covariantTensorDerivative T
  let B := D.covariantTensorDerivative A
  have hA := hD.2.2.1 _ _ hT
  have hB := hD.2.2.1 _ _ hA
  have hcons {V : Type} (z : Fin (k + 2) → V) :
      Fin.cons (z 0) (Fin.cons (z 1) (fun i : Fin k => z i.succ.succ)) = z := by
    ext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  have hswap {V : Type} (p q : V) (w : Fin k → V) :
      Fin.cons p (Fin.cons q w) ∘ Equiv.swap 0 1 = Fin.cons q (Fin.cons p w) :=
    Matrix.cons_cons_comp_swap_zero_one p q w
  have hS : S = fun y z => B y (z ∘ Equiv.swap 0 1) - B y z := by
    funext y z
    have h := D.covariantTensorDerivative_commutator hT y (z 0) (z 1)
      (fun i => z i.succ.succ)
    have hzswap : Fin.cons (z 1) (Fin.cons (z 0) (fun i : Fin k => z i.succ.succ)) =
        z ∘ Equiv.swap 0 1 := by
      have hh := hswap (z 0) (z 1) (fun i => z i.succ.succ)
      rw [hcons] at hh
      exact hh.symm
    simp only [hcons, hzswap] at h
    dsimp only [S, B, A, covariantCurvatureAction]
    linarith only [h]
  have hDS (d p q : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative S x (Fin.cons d (Fin.cons p (Fin.cons q v))) =
        D.covariantTensorDerivative B x (Fin.cons d (Fin.cons q (Fin.cons p v))) -
          D.covariantTensorDerivative B x (Fin.cons d (Fin.cons p (Fin.cons q v))) := by
    rw [hS, D.covariantTensorDerivative_sub (hB.perm (Equiv.swap 0 1)) hB]
    dsimp only
    rw [D.covariantTensorDerivative_reindex]
    congr 2
    exact congrArg (fun w : Fin (k + 2) → TangentSpace (𝓡 n) x =>
      (Fin.cons d w : Fin (k + 3) → TangentSpace (𝓡 n) x))
      (hswap p q v)
  have hpoint (d : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative B x (Fin.cons a (Fin.cons d (Fin.cons d v))) -
        D.covariantTensorDerivative B x (Fin.cons d (Fin.cons d (Fin.cons a v))) =
      -(D.covariantCurvatureAction A x a d (Fin.cons d v) +
        D.covariantTensorDerivative S x (Fin.cons d (Fin.cons a (Fin.cons d v)))) := by
    have h := D.covariantTensorDerivative_commutator hA x a d (Fin.cons d v)
    change D.covariantTensorDerivative B x (Fin.cons a (Fin.cons d (Fin.cons d v))) -
      D.covariantTensorDerivative B x (Fin.cons d (Fin.cons a (Fin.cons d v))) =
      -D.covariantCurvatureAction A x a d (Fin.cons d v) at h
    rw [hDS]
    linarith only [h]
  dsimp only
  rw [D.covariantTensorDerivative_tensorLaplacian hD hT]
  simp only [tensorLaplacian, iteratedCovariantTensorDerivative,
    ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => hpoint _)

end PoincareConjecture.LeviCivitaData
