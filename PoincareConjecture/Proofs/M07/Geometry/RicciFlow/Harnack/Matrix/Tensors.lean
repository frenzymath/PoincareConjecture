import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.RicciDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Algebra
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Hessian.Symmetry
import Mathlib.Tactic.Ring









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


noncomputable def hamiltonP (D : LeviCivitaData g)
    (x : M) (u v w : TangentSpace (𝓡 n) x) : ℝ :=
  D.covariantTensorDerivative D.ricciEvaluation x ![u, v, w] -
    D.covariantTensorDerivative D.ricciEvaluation x ![v, u, w]



noncomputable def hamiltonM (D : LeviCivitaData g) (τ : ℝ)
    (x : M) (u v : TangentSpace (𝓡 n) x) : ℝ :=
  let b := g.orthonormalBasis x
  D.tensorLaplacian D.ricciEvaluation x ![u, v] -
    D.hessian D.scalarCurvature x u v / 2 +
    (2 * (∑ k, ∑ l, D.curvatureTensor x (b k) u (b l) v *
      D.ricci x (b k) (b l)) -
      ∑ k, D.ricci x u (b k) * D.ricci x (b k) v) +
    D.ricci x u v / (2 * τ)

theorem hamiltonP_skew (D : LeviCivitaData g)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    hamiltonP D x u v w = -hamiltonP D x v u w := by
  unfold hamiltonP
  ring

theorem hamiltonP_cyclic (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    hamiltonP D x u v w + hamiltonP D x v w u + hamiltonP D x w u v = 0 := by
  unfold hamiltonP
  rw [D.covariantTensorDerivative_ricciEvaluation_symm hD x v u w,
    D.covariantTensorDerivative_ricciEvaluation_symm hD x w v u,
    D.covariantTensorDerivative_ricciEvaluation_symm hD x u w v]
  ring



lemma hamiltonP_isSmoothCovariantTensor
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) :
    IsSmoothCovariantTensor (k := 3) (fun x v ↦ hamiltonP D x (v 0) (v 1) (v 2)) := by
  have hA := hD.2.2.1 2 D.ricciEvaluation hD.2.1
  have he (x : M) (v : Fin 3 → TangentSpace (𝓡 n) x) :
      ![v 0, v 1, v 2] = v := by
    ext i
    fin_cases i <;> rfl
  have hs (x : M) (v : Fin 3 → TangentSpace (𝓡 n) x) :
      ![v 1, v 0, v 2] = v ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have hp : (fun x (v : Fin 3 → TangentSpace (𝓡 n) x) ↦
      hamiltonP D x (v 0) (v 1) (v 2)) =
      (fun x v ↦ D.covariantTensorDerivative D.ricciEvaluation x v -
        D.covariantTensorDerivative D.ricciEvaluation x (v ∘ Equiv.swap 0 1)) := by
    funext x v
    simp only [hamiltonP, he, hs]
  rw [hp]
  exact hA.sub (hA.perm (Equiv.swap 0 1))


lemma harnackReaction_symm (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    let b := g.orthonormalBasis x
    2 * (∑ k, ∑ l, D.curvatureTensor x (b k) u (b l) v * D.ricci x (b k) (b l)) -
        (∑ k, D.ricci x u (b k) * D.ricci x (b k) v) =
      2 * (∑ k, ∑ l, D.curvatureTensor x (b k) v (b l) u * D.ricci x (b k) (b l)) -
        (∑ k, D.ricci x v (b k) * D.ricci x (b k) u) := by
  let b := g.orthonormalBasis x
  have hs (a c : TangentSpace (𝓡 n) x) : D.ricci x a c = D.ricci x c a :=
    (hD.2.2.2.1 x a c a c).2.2.2
  have hRm : (∑ k, ∑ l, D.curvatureTensor x (b k) u (b l) v *
      D.ricci x (b k) (b l)) =
      ∑ k, ∑ l, D.curvatureTensor x (b k) v (b l) u * D.ricci x (b k) (b l) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [(hD.2.2.2.1 x (b l) u (b k) v).2.1, hs (b l) (b k)]
  have hRic : (∑ k, D.ricci x u (b k) * D.ricci x (b k) v) =
      ∑ k, D.ricci x v (b k) * D.ricci x (b k) u := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hs u (b k), hs (b k) v, mul_comm]
  dsimp only
  rw [hRm, hRic]



lemma hamiltonM_eq_laplacian_add_ricciReaction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (τ : ℝ) (x : M) (u v : TangentSpace (𝓡 n) x) :
    hamiltonM D τ x u v =
      D.tensorLaplacian D.ricciEvaluation x ![u, v] + D.ricciReaction x u v -
        D.hessian D.scalarCurvature x u v / 2 +
        (∑ k, D.ricci x u (g.orthonormalBasis x k) *
          D.ricci x (g.orthonormalBasis x k) v) + D.ricci x u v / (2 * τ) := by
  have hflip (a b c d : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x a b c d = D.curvatureTensor x b a d c := by
    rw [(hD.2.2.2.1 x a b c d).2.1, (hD.2.2.2.1 x c d a b).1,
      (hD.2.2.2.1 x c d b a).2.1, (hD.2.2.2.1 x b a c d).1, neg_neg]
  unfold hamiltonM LeviCivitaData.ricciReaction
  simp_rw [hflip (g.orthonormalBasis x _) u (g.orthonormalBasis x _) v]
  ring



lemma ricci_hasDerivWithinAt_hamiltonM
    (hC : RicciFlowCurvatureTheory.{u}) (J : Set ℝ) (F : RicciFlow n M J)
    (t : ℝ) (ht : t ∈ J) (τ : ℝ)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (F.connection s).ricci x u v)
      (hamiltonM (F.connection t) τ x u v +
        (F.connection t).hessian (F.connection t).scalarCurvature x u v / 2 -
        (∑ k, (F.connection t).ricci x u ((F.metric t).orthonormalBasis x k) *
          (F.connection t).ricci x ((F.metric t).orthonormalBasis x k) v) -
        (F.connection t).ricci x u v / (2 * τ)) J t := by
  apply (hC.ricci_evolution n M J F t ht x u v).congr_deriv
  rw [hamiltonM_eq_laplacian_add_ricciReaction (F.connection t)
    (hC.tensor_calculus n M (F.metric t) (F.connection t))]
  ring



lemma scalarCurvature_contMDiff_slice
    (hC : RicciFlowCurvatureTheory.{u}) (J : Set ℝ) (F : RicciFlow n M J)
    (t : ℝ) (ht : t ∈ J) :
    ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (F.connection t).scalarCurvature := by
  have hs : ContMDiff (𝓡 n) ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ∞ (fun x : M ↦ (t, x)) :=
    (contMDiff_const (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) (c := t)).prodMk
      (contMDiff_id (I := 𝓡 n))
  simpa only [Function.comp_def] using
    (hC.scalar_regular n M J F).comp_contMDiff (f := fun x : M ↦ (t, x))
      hs (fun x ↦ ⟨ht, Set.mem_univ x⟩)



theorem hamiltonM_symm_of_curvatureTheory
    (hC : RicciFlowCurvatureTheory.{u}) (J : Set ℝ) (F : RicciFlow n M J)
    (t : ℝ) (ht : t ∈ J) (τ : ℝ)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    hamiltonM (F.connection t) τ x u v = hamiltonM (F.connection t) τ x v u := by
  have hD := hC.tensor_calculus n M (F.metric t) (F.connection t)
  have hH := (F.connection t).hessian_symm
    (scalarCurvature_contMDiff_slice hC J F t ht) x u v
  unfold hamiltonM
  dsimp only
  rw [(F.connection t).tensorLaplacian_ricciEvaluation_symm hD x u v, hH,
    harnackReaction_symm (F.connection t) hD x u v,
    (hD.2.2.2.1 x u v u v).2.2.2]

end Poincare.RicciFlow.Harnack
