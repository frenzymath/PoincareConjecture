import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Operations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma covariantTensorDerivative_perm (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k) (σ : Equiv.Perm (Fin k))
    (hT : ∀ x v, T x (v ∘ σ) = T x v)
    (x : M) (u : TangentSpace (𝓡 n) x) (v : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative T x (Fin.cons u (v ∘ σ)) =
      D.covariantTensorDerivative T x (Fin.cons u v) := by
  simp only [covariantTensorDerivative, Fin.cons_succ, Fin.cons_zero,
    Function.comp_apply]
  have hvalue : (fun y ↦ T y (fun i ↦
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v (σ i)) y)) =
      (fun y ↦ T y (fun i ↦
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)) := by
    funext y
    exact hT y (fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i) y)
  rw [hvalue]
  congr 1
  calc
    _ = ∑ i, T x (Function.update v (σ i)
        (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n))
          (v (σ i))) x u)) := by
      apply Finset.sum_congr rfl
      intro i _
      have hu (a : TangentSpace (𝓡 n) x) :
          Function.update (fun j ↦ v (σ j)) i a = Function.update v (σ i) a ∘ σ := by
        funext j
        simp only [Function.comp_apply, Function.update_apply, σ.injective.eq_iff]
      have hp := hT x (Function.update v (σ i)
        (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v (σ i))) x u))
      rw [hu]
      exact hp
    _ = _ := Equiv.sum_comp σ (fun i ↦ T x (Function.update v i
      (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i)) x u)))

lemma covariantTensorDerivative_symm_last_three (D : LeviCivitaData g)
    (T : CovariantTensorEvaluation n M 3)
    (hT : ∀ x a b c, T x ![a, b, c] = T x ![a, c, b])
    (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative T x ![u, v, w, z] =
      D.covariantTensorDerivative T x ![u, v, z, w] := by
  have hperm (y : M) (a : Fin 3 → TangentSpace (𝓡 n) y) :
      T y (a ∘ Equiv.swap 1 2) = T y a := by
    have h₁ : a ∘ Equiv.swap 1 2 = ![a 0, a 2, a 1] := by
      ext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    have h₂ : a = ![a 0, a 1, a 2] := by
      ext i
      fin_cases i <;> rfl
    rw [h₁, hT, ← h₂]
  have htail : ![v, z, w] ∘ Equiv.swap (1 : Fin 3) 2 = ![v, w, z] := by
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_def]
  have htuple : Fin.cons u (![v, z, w] ∘ Equiv.swap 1 2) = ![u, v, w, z] := by
    rw [htail, Matrix.Fin.cons_vecCons]
  simpa only [htuple, Matrix.Fin.cons_vecCons] using
    D.covariantTensorDerivative_perm T (Equiv.swap 1 2) hperm x u ![v, z, w]

end PoincareConjecture.LeviCivitaData
