import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Connection.CurvatureFirstVariation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.TensorCommutator
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.RiemannDifferentialContractions
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Reaction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {J : Set ℝ}

set_option backward.isDefEq.respectTransparency false in
private theorem curvature_expand_first (D : LeviCivitaData g) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x a b c d =
      ∑ i, g.inner x (g.orthonormalBasis x i) a *
        D.curvatureTensor x (g.orthonormalBasis x i) b c d := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := g.orthonormalBasis x
  obtain ⟨P, hP⟩ := (isSmoothCovariantTensor_riemannEvaluation D).1 x
  let L := P.toLinearMap ![0, b, c, d] 0
  have hL (a : TangentSpace (𝓡 n) x) : L a = D.curvatureTensor x a b c d := by
    have hu : Function.update ![0, b, c, d] 0 a = ![a, b, c, d] := by
      funext i
      fin_cases i <;> simp [Function.update]
    change P (Function.update ![0, b, c, d] 0 a) = D.curvatureTensor x a b c d
    rw [hu]
    exact (hP ![a, b, c, d]).symm
  calc
    _ = L a := (hL a).symm
    _ = L (∑ i, inner ℝ (e i) a • e i) := congrArg L (e.sum_repr' a).symm
    _ = ∑ i, inner ℝ (e i) a * D.curvatureTensor x (e i) b c d := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, hL]
      rfl
    _ = _ := rfl

set_option maxHeartbeats 2500000 in

set_option backward.isDefEq.respectTransparency false in
private theorem curvature_action_trace (D : LeviCivitaData g) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    (∑ i, (D.curvatureTensor x (D.curvature x a (e i) (e i)) b c d +
      D.curvatureTensor x (e i) (D.curvature x a (e i) b) c d +
      D.curvatureTensor x (e i) b (D.curvature x a (e i) c) d +
      D.curvatureTensor x (e i) b c (D.curvature x a (e i) d))) -
      (∑ i, (D.curvatureTensor x (D.curvature x b (e i) (e i)) a c d +
        D.curvatureTensor x (e i) (D.curvature x b (e i) a) c d +
        D.curvatureTensor x (e i) a (D.curvature x b (e i) c) d +
        D.curvatureTensor x (e i) a c (D.curvature x b (e i) d))) =
      (∑ i, (D.ricci x a (e i) * D.curvatureTensor x (e i) b c d +
        D.ricci x b (e i) * D.curvatureTensor x a (e i) c d)) -
      2 * (D.curvatureB x a b c d - D.curvatureB x a b d c -
        D.curvatureB x a d b c + D.curvatureB x a c b d) := by
  classical
  let e := g.orthonormalBasis x
  let E := TangentSpace (𝓡 n) x
  let R := D.curvatureTensor x
  let K := D.curvature x
  let B := D.curvatureB x
  have hswap (a b c d : E) : R a b c d = -R b a c d :=
    curvatureTensor_swap_first D x b a c d
  have hlast (a b c d : E) : R a b c d = -R a b d c :=
    curvatureTensor_swap_last D x a b c d
  have hpair (a b c d : E) : R a b c d = R c d a b :=
    curvatureTensor_pair_exchange D x a b c d
  have hBianchi (a b c d : E) : R a b c d = R a c b d - R a d b c := by
    have h := curvatureTensor_cyclic D x a b c d
    change R a b c d + R b c a d + R c a b d = 0 at h
    rw [hpair b c a d, hswap c a b d] at h
    linarith only [h]
  have hcoeff (a b c : E) (i) : g.inner x (e i) (K a b c) = R a b (e i) c := by
    rw [g.symm]
    rfl
  have hR1 (v a c d : E) : R v a c d = ∑ i, g.inner x (e i) v * R (e i) a c d :=
    curvature_expand_first D x v a c d
  have hR2 (v a c d : E) : R a v c d = ∑ i, g.inner x (e i) v * R a (e i) c d := by
    calc
      _ = -R v a c d := hswap a v c d
      _ = -(∑ i, g.inner x (e i) v * R (e i) a c d) := congrArg Neg.neg (hR1 v a c d)
      _ = _ := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hswap (e i) a c d]
        ring
  have hR3 (v a b d : E) : R a b v d = ∑ i, g.inner x (e i) v * R a b (e i) d := by
    rw [hpair a b v d, hR1 v d a b]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hpair (e i) d a b]
  have hR4 (v a b c : E) : R a b c v = ∑ i, g.inner x (e i) v * R a b c (e i) := by
    rw [hpair a b c v, hR2 v c a b]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hpair c (e i) a b]
  have hBpair (a b c d : E) : B a b c d = B c d a b := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  have hBswap (a b c d : E) : B b a c d = B a b d c := by
    change (∑ i, ∑ j, R b (e i) a (e j) * R c (e i) d (e j)) =
      ∑ i, ∑ j, R a (e i) b (e j) * R d (e i) c (e j)
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hpair b (e j) a (e i), hpair c (e j) d (e i)]
  have h0 (a b c d : E) :
      (∑ i, R (K a (e i) (e i)) b c d) =
        ∑ i, D.ricci x a (e i) * R (e i) b c d := by
    calc
      _ = ∑ i, ∑ j, R a (e i) (e j) (e i) * R (e j) b c d := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hR1 (K a (e i) (e i)) b c d]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoeff]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_mul]
        rfl
  have h1 (a b c d : E) :
      (∑ i, R (e i) (K a (e i) b) c d) = -(B a b c d - B a b d c) := by
    change (∑ i, R (e i) (K a (e i) b) c d) =
      -((∑ i, ∑ j, R a (e i) b (e j) * R c (e i) d (e j)) -
        ∑ i, ∑ j, R a (e i) b (e j) * R d (e i) c (e j))
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hR2 (K a (e i) b) (e i) c d,
      ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoeff, hlast a (e i) (e j) b, hpair (e i) (e j) c d,
      hBianchi c d (e i) (e j), hpair c (e j) d (e i)]
    ring
  have h2 (a b c d : E) :
      (∑ i, R (e i) b (K a (e i) c) d) = -B a c b d := by
    change (∑ i, R (e i) b (K a (e i) c) d) =
      -(∑ i, ∑ j, R a (e i) c (e j) * R b (e i) d (e j))
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hR3 (K a (e i) c) (e i) b d, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoeff, hlast a (e i) (e j) c, hswap (e i) b (e j) d,
      hlast b (e i) (e j) d]
    ring
  have h3 (a b c d : E) :
      (∑ i, R (e i) b c (K a (e i) d)) = B a d b c := by
    change (∑ i, R (e i) b c (K a (e i) d)) =
      ∑ i, ∑ j, R a (e i) d (e j) * R b (e i) c (e j)
    apply Finset.sum_congr rfl
    intro i hi
    rw [hR4 (K a (e i) d) (e i) b c]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoeff, hlast a (e i) (e j) d, hswap (e i) b c (e j)]
    ring
  have h0b : (∑ i, D.ricci x b (e i) * R (e i) a c d) =
      -(∑ i, D.ricci x b (e i) * R a (e i) c d) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hswap (e i) a c d]
    ring
  change (∑ i, (R (K a (e i) (e i)) b c d + R (e i) (K a (e i) b) c d +
      R (e i) b (K a (e i) c) d + R (e i) b c (K a (e i) d))) -
    (∑ i, (R (K b (e i) (e i)) a c d + R (e i) (K b (e i) a) c d +
      R (e i) a (K b (e i) c) d + R (e i) a c (K b (e i) d))) =
    (∑ i, (D.ricci x a (e i) * R (e i) b c d + D.ricci x b (e i) * R a (e i) c d)) -
      2 * (B a b c d - B a b d c - B a d b c + B a c b d)
  simp only [Finset.sum_add_distrib, h0, h1, h2, h3]
  rw [h0b, hBswap a b c d, hBswap a b d c,
    hBpair b c a d, hBpair b d a c]
  ring

private theorem cons_cons_four_tuple {α : Type*} (p q a b c d : α) :
    Fin.cons p (Fin.cons q ![a, b, c, d]) = ![p, q, a, b, c, d] := by
  funext i
  fin_cases i <;> rfl

private theorem cons_cons_two_tuple {α : Type*} (p q a b : α) :
    Fin.cons p (Fin.cons q ![a, b]) = ![p, q, a, b] := by
  funext i
  fin_cases i <;> rfl

set_option maxHeartbeats 4000000 in

set_option backward.isDefEq.respectTransparency false in
theorem curvature_firstVariation_eq_laplacian_add_reaction (D : LeviCivitaData g) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    -2 * D.ricci x (D.curvature x a b d) c -
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, b, d, c] -
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, d, b, c] +
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, c, b, d] +
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, a, d, c] +
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, d, a, c] -
      D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, c, a, d] =
      D.tensorLaplacian D.riemannEvaluation x ![a, b, c, d] + D.curvatureReaction x a b c d := by
  classical
  let E := TangentSpace (𝓡 n) x
  let e := g.orthonormalBasis x
  let R := D.curvatureTensor x
  let K := D.curvature x
  let H := D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
  let T := D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x
  let L := D.tensorLaplacian D.riemannEvaluation x ![a, b, c, d]
  let A (p q u v w z : E) := R (K p q u) v w z + R u (K p q v) w z +
    R u v (K p q w) z + R u v w (K p q z)
  let C := (∑ i, A a (e i) (e i) b c d) - ∑ i, A b (e i) (e i) a c d
  let F4 := H ![a, c, b, d] - H ![a, d, b, c] - H ![b, c, a, d] + H ![b, d, a, c]
  have hComm (p q u v w z : E) :
      T ![p, q, u, v, w, z] - T ![q, p, u, v, w, z] = -A p q u v w z := by
    have hc := covariantTensorDerivative_commutator D
      (isSmoothCovariantTensor_riemannEvaluation D) x p q ![u, v, w, z]
    rw [cons_cons_four_tuple, cons_cons_four_tuple, Fin.sum_univ_four] at hc
    simpa [A, R, K, LeviCivitaData.riemannEvaluation, Function.update] using hc
  have hCommSum (p q c d : E) :
      (∑ i, T ![p, e i, e i, q, c, d]) - (∑ i, T ![e i, p, e i, q, c, d]) =
        -(∑ i, A p (e i) (e i) q c d) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact hComm p (e i) (e i) q c d
  have hdiv (p q c d : E) :
      (∑ i, T ![p, e i, e i, q, c, d]) = H ![p, c, q, d] - H ![p, d, q, c] := by
    have hd := riemann_secondCovariantDerivative_divergence D x p q c d
    rw [ricci_secondCovariantDerivative_symm D x p c d q,
      ricci_secondCovariantDerivative_symm D x p d c q] at hd
    exact hd
  have hLtrace : L = ∑ i, T ![e i, e i, a, b, c, d] := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x)
      (cons_cons_four_tuple (e i) (e i) a b c d)
  have hBianchi : (∑ i, T ![e i, e i, a, b, c, d]) -
      (∑ i, T ![e i, a, e i, b, c, d]) + (∑ i, T ![e i, b, e i, a, c, d]) = 0 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i hi
    have hb := riemann_secondCovariantDerivative_bianchi D x (e i) (e i) a b c d
    rw [riemann_secondCovariantDerivative_swap_first D x (e i) a b (e i) c d] at hb
    exact hb
  have hLap : L = F4 + C := by
    have hca := hCommSum a b c d
    have hcb := hCommSum b a c d
    rw [hdiv] at hca hcb
    rw [← hLtrace] at hBianchi
    dsimp only [F4, C]
    linarith only [hBianchi, hca, hcb]
  have hRicComm : H ![a, b, d, c] - H ![b, a, d, c] =
      -(D.ricci x (K a b d) c + D.ricci x d (K a b c)) := by
    have hc := covariantTensorDerivative_commutator D
      (isSmoothCovariantTensor_ricciEvaluation D) x a b ![d, c]
    rw [cons_cons_two_tuple, cons_cons_two_tuple, Fin.sum_univ_two] at hc
    simpa [K, LeviCivitaData.ricciEvaluation, Function.update] using hc
  have hcoeff (u v w : E) (i) : g.inner x (e i) (K u v w) = R u v (e i) w := by
    rw [g.symm]
    rfl
  have hRicK (u v w z : E) :
      D.ricci x (K u v w) z = ∑ i, R u v (e i) w * D.ricci x (e i) z := by
    change (∑ j, R (K u v w) (e j) z (e j)) = _
    calc
      _ = ∑ j, ∑ i, R u v (e i) w * R (e i) (e j) z (e j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have he := curvature_expand_first D x (K u v w) (e j) z (e j)
        change R (K u v w) (e j) z (e j) =
          ∑ i, g.inner x (e i) (K u v w) * R (e i) (e j) z (e j) at he
        rw [he]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoeff]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum]
        rfl
  have hmetric1 : D.ricci x (K a b d) c =
      ∑ i, D.ricci x c (e i) * R a b (e i) d := by
    rw [hRicK]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ricci_symm D x (e i) c]
    exact mul_comm _ _
  have hmetric2 : D.ricci x d (K a b c) =
      -(∑ i, D.ricci x d (e i) * R a b c (e i)) := by
    rw [ricci_symm D x d (K a b c), hRicK, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ricci_symm D x (e i) d]
    have hs : R a b (e i) c = -R a b c (e i) :=
      curvatureTensor_swap_last D x a b (e i) c
    rw [hs]
    ring
  have hC : C = (∑ i, (D.ricci x a (e i) * R (e i) b c d +
      D.ricci x b (e i) * R a (e i) c d)) -
      2 * (D.curvatureB x a b c d - D.curvatureB x a b d c -
        D.curvatureB x a d b c + D.curvatureB x a c b d) :=
    curvature_action_trace D x a b c d
  have hReaction : -C - D.ricci x (K a b d) c + D.ricci x d (K a b c) =
      D.curvatureReaction x a b c d := by
    rw [hC, hmetric1, hmetric2]
    simp only [LeviCivitaData.curvatureReaction, Finset.sum_add_distrib]
    ring
  change -2 * D.ricci x (K a b d) c - H ![a, b, d, c] - H ![a, d, b, c] +
    H ![a, c, b, d] + H ![b, a, d, c] + H ![b, d, a, c] - H ![b, c, a, d] =
      L + D.curvatureReaction x a b c d
  dsimp only [F4] at hLap
  linarith only [hLap, hRicComm, hReaction]

theorem hasDerivAt_curvatureTensor_evolution (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s ↦ (F.connection s).curvatureTensor x u v w z)
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x ![u, v, w, z] +
        (F.connection t).curvatureReaction x u v w z) t := by
  exact (hasDerivAt_curvatureTensor_first_variation F ht x u v w z).congr_deriv
    (curvature_firstVariation_eq_laplacian_add_reaction (F.connection t) x u v w z)

end PoincareConjecture.RicciFlowAnalysis
