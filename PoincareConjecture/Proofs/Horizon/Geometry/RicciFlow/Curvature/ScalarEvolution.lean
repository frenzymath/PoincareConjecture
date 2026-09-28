import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.ScalarEvolution.CurvatureVariation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.TimeDerivative.Trace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace RicciFlow

variable {J : Set ℝ}

private noncomputable def ricciVariation (F : RicciFlow n M J) (t : ℝ) :
    CovariantTensorEvaluation n M 2 := fun x v =>
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  (∑ i, (-2 * D.ricci x (D.curvature x (v 0) (b i) (b i)) (v 1) +
    D.covariantTensorDerivative D.ricciConnectionVariation x ![v 0, b i, b i, v 1] -
    D.covariantTensorDerivative D.ricciConnectionVariation x ![b i, v 0, b i, v 1])) +
  2 * ∑ i, ∑ j, D.ricci x (b i) (b j) * D.curvatureTensor x (v 0) (b i) (v 1) (b j)

private theorem hasDerivAt_ricci_connectionVariation
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    (x : M) (v : Fin 2 → TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => (F.connection s).ricciEvaluation x v)
      (ricciVariation F t x v) t := by
  let σ : Equiv.Perm (Fin 4) :=
    { toFun := ![2, 0, 3, 1]
      invFun := ![1, 3, 0, 2]
      left_inv := by decide
      right_inv := by decide }
  let T : ℝ → CovariantTensorEvaluation n M 4 := fun s y w =>
    (F.connection s).riemannEvaluation y (w ∘ σ)
  let W : ℝ → CovariantTensorEvaluation n M 4 := fun _ y w =>
    let D := F.connection t;
    -2 * D.ricci y (D.curvature y (w 2) (w 0) (w 1)) (w 3) +
      D.covariantTensorDerivative D.ricciConnectionVariation y ![w 2, w 0, w 1, w 3] -
      D.covariantTensorDerivative D.ricciConnectionVariation y ![w 0, w 2, w 1, w 3]
  have hW (z : Fin 4 → TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s => T s x z) (W t x z) t :=
    F.hasDerivAt_curvatureTensor_connectionVariation ht x (z 2) (z 0) (z 3) (z 1)
  have h := F.hasDerivAt_tensorTrace (T := T) (W := W) ht x
    (fun s => (F.connection s).riemannEvaluation_isSmooth_manifold.perm σ) hW v
  have htrace (s : ℝ) : (F.metric s).tensorTrace (T s) x v =
      (F.connection s).ricciEvaluation x v := rfl
  simp_rw [htrace] at h
  apply h.congr_deriv
  rfl

end RicciFlow

namespace LeviCivitaData

variable {g : RiemannianMetric n M}

private theorem sum_ricci_curvature_eq_sum_ricci_sq (D : LeviCivitaData g) (x : M) :
    (∑ i, ∑ j, D.ricci x
      (D.curvature x (g.orthonormalBasis x i) (g.orthonormalBasis x j)
        (g.orthonormalBasis x j)) (g.orthonormalBasis x i)) = D.ricciNormSq x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  obtain ⟨A, hA⟩ := D.ricciEvaluation_isSmooth_manifold.1 x
  let B := bilinearOfTwoTensor A
  have hB (a c : TangentSpace (𝓡 n) x) : B a c = D.ricci x a c := (hA ![a, c]).symm
  have hexp (a c : TangentSpace (𝓡 n) x) :
      D.ricci x a c = ∑ k, g.inner x a (b k) * D.ricci x (b k) c := by
    conv_lhs => rw [← hB, ← b.sum_repr' a]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      hB, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [real_inner_comm]
    rfl
  change (∑ i, ∑ j, D.ricci x (D.curvature x (b i) (b j) (b j)) (b i)) = _
  conv_lhs => arg 2; ext i; arg 2; ext j; rw [hexp]
  change (∑ i, ∑ j, ∑ k,
    D.curvatureTensor x (b i) (b j) (b k) (b j) * D.ricci x (b k) (b i)) = _
  calc
    _ = ∑ i, ∑ k, D.ricci x (b i) (b k) * D.ricci x (b k) (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ricci, b]
    _ = D.ricciNormSq x := by
      unfold ricciNormSq
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [D.ricci_symmetric x (b j) (b i)]
      exact (pow_two _).symm

private theorem sum_ricci_curvature_contraction (D : LeviCivitaData g) (x : M) :
    (∑ k, ∑ i, ∑ j,
      D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x j) *
        D.curvatureTensor x (g.orthonormalBasis x k) (g.orthonormalBasis x i)
          (g.orthonormalBasis x k) (g.orthonormalBasis x j)) = D.ricciNormSq x := by
  let b := g.orthonormalBasis x
  change (∑ k, ∑ i, ∑ j, D.ricci x (b i) (b j) *
    D.curvatureTensor x (b k) (b i) (b k) (b j)) = _
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, ∑ j, D.ricci x (b i) (b j) * D.ricci x (b i) (b j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum]
      congr 1
      unfold ricci
      apply Finset.sum_congr rfl
      intro k _
      rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last x (b i)]
      simp only [neg_neg]
      rfl
    _ = D.ricciNormSq x := by simp only [ricciNormSq, pow_two, b]

private theorem sum_connectionVariation_derivative_eq_laplacian (D : LeviCivitaData g) (x : M) :
    (∑ i, ∑ j,
      (D.covariantTensorDerivative D.ricciConnectionVariation x
        ![g.orthonormalBasis x i, g.orthonormalBasis x j,
          g.orthonormalBasis x j, g.orthonormalBasis x i] -
      D.covariantTensorDerivative D.ricciConnectionVariation x
        ![g.orthonormalBasis x j, g.orthonormalBasis x i,
          g.orthonormalBasis x j, g.orthonormalBasis x i])) =
      D.laplacian D.scalarCurvature x := by
  simp only [Finset.sum_sub_distrib,
    D.sum_covariantDerivative_ricciConnectionVariation_first_two,
    zero_sub, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp only [D.sum_covariantDerivative_ricciConnectionVariation_first_last,
    Finset.sum_neg_distrib, neg_neg, laplacian]

end LeviCivitaData

namespace RicciFlow

variable {J : Set ℝ}

theorem hasDerivAt_scalarCurvature
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M) :
    HasDerivAt (fun s => (F.connection s).scalarCurvature x)
      ((F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x) t := by
  let T : ℝ → CovariantTensorEvaluation n M 2 := fun s => (F.connection s).ricciEvaluation
  let W : ℝ → CovariantTensorEvaluation n M 2 := fun _ => ricciVariation F t
  have h := F.hasDerivAt_tensorTrace (T := T) (W := W) ht x
    (fun s => (F.connection s).ricciEvaluation_isSmooth_manifold)
    (F.hasDerivAt_ricci_connectionVariation ht x) Fin.elim0
  change HasDerivAt (fun s => (F.connection s).scalarCurvature x) _ t at h
  apply h.congr_deriv
  let D := F.connection t
  have hnorm : (∑ i, ∑ j, D.ricci x ((F.metric t).orthonormalBasis x i)
      ((F.metric t).orthonormalBasis x j) * D.ricci x ((F.metric t).orthonormalBasis x i)
      ((F.metric t).orthonormalBasis x j)) = D.ricciNormSq x := by
    simp only [LeviCivitaData.ricciNormSq, pow_two]
  change (∑ i, ricciVariation F t x
    ![(F.metric t).orthonormalBasis x i, (F.metric t).orthonormalBasis x i]) +
      2 * (∑ i, ∑ j, D.ricci x ((F.metric t).orthonormalBasis x i)
        ((F.metric t).orthonormalBasis x j) * D.ricci x ((F.metric t).orthonormalBasis x i)
        ((F.metric t).orthonormalBasis x j)) = _
  rw [hnorm]
  simp only [ricciVariation, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hconn := D.sum_connectionVariation_derivative_eq_laplacian x
  simp only [Finset.sum_sub_distrib] at hconn
  have hcurv := D.sum_ricci_curvature_eq_sum_ricci_sq x
  have hreaction := D.sum_ricci_curvature_contraction x
  dsimp only [D] at hconn hcurv hreaction hnorm ⊢
  rw [hcurv, hreaction]
  linarith

end RicciFlow

end PoincareConjecture
