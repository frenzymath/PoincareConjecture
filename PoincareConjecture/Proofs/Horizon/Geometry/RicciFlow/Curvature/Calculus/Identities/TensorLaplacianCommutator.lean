import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.TensorLaplacianDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.ThirdCovariantDerivativeCommutator











set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem multilinear_curvature_update (D : LeviCivitaData g)
    {k : ℕ} (x : M)
    (A : MultilinearMap ℝ (fun _ : Fin k ↦ TangentSpace (𝓡 n) x) ℝ)
    (a d : TangentSpace (𝓡 n) x)
    (v : Fin k → TangentSpace (𝓡 n) x) (r : Fin k) :
    let b := g.orthonormalBasis x
    A (Function.update v r (D.curvature x a d (v r))) =
      ∑ q, D.curvatureTensor x a d (b q) (v r) *
        A (Function.update v r (b q)) := by
  classical
  dsimp only
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb : (∑ q, D.curvatureTensor x a d (b q) (v r) • b q) =
      D.curvature x a d (v r) := by
    change (∑ q, inner ℝ (D.curvature x a d (v r)) (b q) • b q) = _
    simpa only [real_inner_comm] using b.sum_repr' (D.curvature x a d (v r))
  conv_lhs => rw [← hb]
  simp only [A.map_update_sum, A.map_update_smul, smul_eq_mul, b]

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem covariantTensorDerivative_tensorLaplacian_commutator
    (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    (x : M) (a : TangentSpace (𝓡 n) x)
    (v : Fin k → TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    let K := D.covariantTensorDerivative T
    D.covariantTensorDerivative (D.tensorLaplacian T) x (Fin.cons a v) -
      D.tensorLaplacian K x (Fin.cons a v) =
      -(∑ p, ∑ q,
        D.curvatureTensor x a (b p) (b q) (b p) *
          K x (Fin.cons (b q) v)) -
      2 * (∑ p, ∑ r, ∑ q,
        D.curvatureTensor x a (b p) (b q) (v r) *
          K x (Fin.cons (b p) (Function.update v r (b q)))) -
      (∑ p, ∑ r, ∑ q,
        D.covariantTensorDerivative D.riemannEvaluation x
          ![b p, a, b p, b q, v r] *
          T x (Function.update v r (b q))) := by
  classical
  dsimp only
  let b := g.orthonormalBasis x
  let K := D.covariantTensorDerivative T
  let C := D.iteratedCovariantTensorDerivative T 3 x
  have hK : IsSmoothCovariantTensor K :=
    isSmoothCovariantTensor_covariantTensorDerivative D hT
  obtain ⟨L, hL⟩ := hK.1 x
  have hpoint (p : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      C (Fin.cons a (Fin.cons (b p) (Fin.cons (b p) v))) -
        C (Fin.cons (b p) (Fin.cons (b p) (Fin.cons a v))) =
        -(∑ q, D.curvatureTensor x a (b p) (b q) (b p) *
          K x (Fin.cons (b q) v)) -
        2 * (∑ r, ∑ q, D.curvatureTensor x a (b p) (b q) (v r) *
          K x (Fin.cons (b p) (Function.update v r (b q)))) -
        (∑ r, ∑ q,
          D.covariantTensorDerivative D.riemannEvaluation x
            ![b p, a, b p, b q, v r] *
            T x (Function.update v r (b q))) := by
    have hfirst := covariantTensorDerivative_commutator D hK x a (b p)
      (Fin.cons (b p) v)
    have hInsert (r : Fin (k + 1)) :
        K x (Function.update (Fin.cons (b p) v) r
          (D.curvature x a (b p)
            ((Fin.cons (b p) v : Fin (k + 1) → TangentSpace (𝓡 n) x) r))) =
          ∑ q, D.curvatureTensor x a (b p) (b q)
            ((Fin.cons (b p) v : Fin (k + 1) → TangentSpace (𝓡 n) x) r) *
            K x (Function.update (Fin.cons (b p) v) r (b q)) := by
      simpa only [hL] using
        multilinear_curvature_update D x L a (b p) (Fin.cons (b p) v) r
    simp only [hInsert] at hfirst
    rw [Fin.sum_univ_succ] at hfirst
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero,
      ← Fin.cons_update] at hfirst
    change C (Fin.cons a (Fin.cons (b p) (Fin.cons (b p) v))) -
      C (Fin.cons (b p) (Fin.cons a (Fin.cons (b p) v))) = _ at hfirst
    have hsecond := thirdCovariantTensorDerivative_commutator D hT x (b p) a (b p) v
    simp only [Finset.sum_add_distrib] at hsecond
    change C (Fin.cons (b p) (Fin.cons a (Fin.cons (b p) v))) -
      C (Fin.cons (b p) (Fin.cons (b p) (Fin.cons a v))) = _ at hsecond
    linarith only [hfirst, hsecond]
  rw [covariantTensorDerivative_tensorLaplacian D hT]
  change (∑ p, C (Fin.cons a (Fin.cons (b p) (Fin.cons (b p) v)))) -
    (∑ p, C (Fin.cons (b p) (Fin.cons (b p) (Fin.cons a v)))) = _
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, b, K]


end PoincareConjecture.RicciFlowAnalysis
