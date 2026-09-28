import PoincareConjecture.Proofs.M04.ScalarContractions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem derivative_neg (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (x : M)
    (v : Fin (k + 1) → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative (fun y w => -T y w) x v =
      -D.covariantTensorDerivative T x v := by
  simp only [LeviCivitaData.covariantTensorDerivative, mvfderiv_fun_neg,
    neg_apply, Finset.sum_neg_distrib]
  ring

theorem riemannDerivative_swap_first (D : LeviCivitaData g) (x : M)
    (a b c d e : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e] =
      -D.covariantTensorDerivative D.riemannEvaluation x ![a, c, b, d, e] := by
  classical
  let s := Equiv.swap (0 : Fin 4) 1
  have he : M04.tensorPermute D.riemannEvaluation s =
      fun y w => -D.riemannEvaluation y w := by
    funext y w
    change D.curvatureTensor y (w (s 0)) (w (s 1)) (w (s 2)) (w (s 3)) = _
    simp only [s, Equiv.swap_apply_def]
    exact M04.curvatureTensor_swap_first D y (w 0) (w 1) (w 2) (w 3)
  have hv : ![b, c, d, e] ∘ s = ![c, b, d, e] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hp := M04.covariantTensorDerivative_tensorPermute D
    (M04.isSmoothCovariantTensor_riemannEvaluation D) s x a ![b, c, d, e]
  rw [he, derivative_neg, hv] at hp
  change -D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e] =
    D.covariantTensorDerivative D.riemannEvaluation x ![a, c, b, d, e] at hp
  linarith only [hp]

theorem riemannDerivative_swap_last (D : LeviCivitaData g) (x : M)
    (a b c d e : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e] =
      -D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, e, d] := by
  classical
  let s := Equiv.swap (2 : Fin 4) 3
  have he : M04.tensorPermute D.riemannEvaluation s =
      fun y w => -D.riemannEvaluation y w := by
    funext y w
    change D.curvatureTensor y (w (s 0)) (w (s 1)) (w (s 2)) (w (s 3)) = _
    simp only [s, Equiv.swap_apply_def]
    exact M04.curvatureTensor_swap_last D y (w 0) (w 1) (w 3) (w 2)
  have hv : ![b, c, d, e] ∘ s = ![b, c, e, d] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hp := M04.covariantTensorDerivative_tensorPermute D
    (M04.isSmoothCovariantTensor_riemannEvaluation D) s x a ![b, c, d, e]
  rw [he, derivative_neg, hv] at hp
  change -D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e] =
    D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, e, d] at hp
  linarith only [hp]

theorem riemannDerivative_pair_exchange (D : LeviCivitaData g) (x : M)
    (a b c d e : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.riemannEvaluation x ![a, b, c, d, e] =
      D.covariantTensorDerivative D.riemannEvaluation x ![a, d, e, b, c] := by
  classical
  let s := (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (1 : Fin 4) 3)
  have he : M04.tensorPermute D.riemannEvaluation s = D.riemannEvaluation := by
    funext y w
    change D.curvatureTensor y (w (s 0)) (w (s 1)) (w (s 2)) (w (s 3)) = _
    simp only [s, Equiv.trans_apply, Equiv.swap_apply_def]
    exact M04.curvatureTensor_pair_exchange D y (w 2) (w 3) (w 0) (w 1)
  have hv : ![b, c, d, e] ∘ s = ![d, e, b, c] := by
    funext i
    fin_cases i <;> simp [s, Equiv.swap_apply_def]
  have hp := M04.covariantTensorDerivative_tensorPermute D
    (M04.isSmoothCovariantTensor_riemannEvaluation D) s x a ![b, c, d, e]
  rw [he, hv] at hp
  exact hp

theorem killing_riemannDerivative_divergence (D : LeviCivitaData g) (x : M)
    (a b c : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative D.riemannEvaluation x
      ![g.orthonormalBasis x i, a, g.orthonormalBasis x i, b, c]) =
      D.covariantTensorDerivative D.ricciEvaluation x ![c, b, a] -
        D.covariantTensorDerivative D.ricciEvaluation x ![b, c, a] := by
  let e := g.orthonormalBasis x
  let R := D.covariantTensorDerivative D.riemannEvaluation x
  let S := D.covariantTensorDerivative D.ricciEvaluation x
  have hzero : (∑ i, (R ![e i, b, c, e i, a] +
      R ![b, c, e i, e i, a] + R ![c, e i, b, e i, a])) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact M04.riemann_second_bianchi D x (e i) b c (e i) a
  have hfirst (i) : R ![e i, b, c, e i, a] = -R ![e i, a, e i, b, c] := by
    dsimp only [R]
    rw [riemannDerivative_pair_exchange]
    exact riemannDerivative_swap_first D x (e i) (e i) a b c
  have hsecond : (∑ i, R ![b, c, e i, e i, a]) = -S ![b, c, a] := by
    dsimp only [R, S, e]
    rw [M04.ricci_covariantDerivative_curvature_trace, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact riemannDerivative_swap_last D x b c (e i) (e i) a
  have hthird : (∑ i, R ![c, e i, b, e i, a]) = S ![c, b, a] := by
    dsimp only [R, S, e]
    rw [M04.ricci_covariantDerivative_curvature_trace]
    apply Finset.sum_congr rfl
    intro i _
    rw [riemannDerivative_swap_first, riemannDerivative_swap_last, neg_neg]
  simp only [hfirst, Finset.sum_add_distrib, Finset.sum_neg_distrib, hsecond, hthird] at hzero
  change (∑ i, R ![e i, a, e i, b, c]) = S ![c, b, a] - S ![b, c, a]
  linarith only [hzero]

end PoincareConjecture.M35.Uniqueness
