import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Tensors
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Tensor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Variation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Regularity

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {J : Set ℝ}

lemma metric_inner_hasDerivWithinAt_ricci
    (F : RicciFlow n M J) (t : ℝ) (ht : t ∈ J)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (F.metric s).inner x u v)
      (-2 * (F.connection t).ricci x u v) J t := by
  exact F.equation t ht x u v

lemma hasDerivAt_hamiltonP_raw
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X Y Z : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    HasDerivAt
      (fun s => mvfderiv (𝓡 n)
        (fun y => (F.connection s).ricci y (Y y) (Z y)) x (X x) -
        mvfderiv (𝓡 n)
          (fun y => (F.connection s).ricci y (X y) (Z y)) x (Y x))
      (mvfderiv (𝓡 n) (fun y =>
        (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation y
            ![Y y, Z y] + (F.connection t).ricciReaction y (Y y) (Z y)) x (X x) -
        mvfderiv (𝓡 n) (fun y =>
        (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation y
            ![X y, Z y] + (F.connection t).ricciReaction y (X y) (Z y)) x (Y x)) t := by
  exact (PoincareConjecture.RicciFlow.hasDerivAt_mvfderiv_ricci_fields
      hC F ht hY hZ (X x)).sub
    (PoincareConjecture.RicciFlow.hasDerivAt_mvfderiv_ricci_fields
      hC F ht hX hZ (Y x))

lemma hamiltonP_eq_raw_sub_connection
    (D : LeviCivitaData g) (x : M) (u v w : TangentSpace (𝓡 n) x) :
    let X := fun a : TangentSpace (𝓡 n) x =>
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
    hamiltonP D x u v w =
      (mvfderiv (𝓡 n) (fun y => D.ricci y (X v y) (X w y)) x u -
        mvfderiv (𝓡 n) (fun y => D.ricci y (X u y) (X w y)) x v) -
      (D.ricci x (D.connection (X v) x u) w +
        D.ricci x v (D.connection (X w) x u)) +
      (D.ricci x (D.connection (X u) x v) w +
        D.ricci x u (D.connection (X w) x v)) := by
  simp [hamiltonP, LeviCivitaData.covariantTensorDerivative,
    LeviCivitaData.ricciEvaluation, Fin.sum_univ_two]
  ring

lemma connection_hasDerivAt_ricci
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M) (v : TangentSpace (𝓡 n) x) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    ∃ A : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x,
      HasDerivAt (fun s => (F.connection s).connection
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x) A t ∧
      ∀ u w : TangentSpace (𝓡 n) x,
        (F.metric t).inner x (A u) w =
          -(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![u, v, w] -
            (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![v, u, w] +
            (F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation x ![w, u, v] :=
  F.connection_hasDerivAt_ricci ht
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) x v

lemma covariantTensorDerivative_hamiltonP
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (a u v w : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative
        (fun y z ↦ hamiltonP D y (z 0) (z 1) (z 2)) x ![a, u, v, w] =
      D.covariantTensorDerivative (D.covariantTensorDerivative D.ricciEvaluation)
          x ![a, u, v, w] -
        D.covariantTensorDerivative (D.covariantTensorDerivative D.ricciEvaluation)
          x ![a, v, u, w] := by
  have hA := hD.2.2.1 2 D.ricciEvaluation hD.2.1
  have hp : (fun y (z : Fin 3 → TangentSpace (𝓡 n) y) ↦
      hamiltonP D y (z 0) (z 1) (z 2)) =
      (fun y z ↦ D.covariantTensorDerivative D.ricciEvaluation y z -
        D.covariantTensorDerivative D.ricciEvaluation y (z ∘ Equiv.swap 0 1)) := by
    funext y z
    have he : ![z 0, z 1, z 2] = z := by
      ext i
      fin_cases i <;> rfl
    have hs : ![z 1, z 0, z 2] = z ∘ Equiv.swap 0 1 := by
      ext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    simp only [hamiltonP, he, hs]
  rw [hp, D.covariantTensorDerivative_sub hA (hA.perm (Equiv.swap 0 1))]
  dsimp only
  rw [D.covariantTensorDerivative_reindex (D.covariantTensorDerivative D.ricciEvaluation)
    (Equiv.swap 0 1) x ![a, u, v, w]]
  congr 2
  ext i
  fin_cases i <;> simp [Equiv.swap_apply_def] <;> rfl

end Poincare.RicciFlow.Harnack
