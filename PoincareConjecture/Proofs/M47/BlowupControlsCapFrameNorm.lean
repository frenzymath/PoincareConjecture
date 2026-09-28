import PoincareConjecture.Proofs.M47.BlowupControlsCapThreeArrays

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem cap_frameGram_eq_identity (g : RiemannianMetric n M) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (he : ∀ v w, g.inner x (e v) (e w) = inner ℝ v w) :
    M04.frameGramOperator g x e.toContinuousLinearMap = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  exact cap_frameGram_inner g x e.toContinuousLinearMap v w |>.trans (he v w)

theorem cap_frameInverseGram_eq_ite (g : RiemannianMetric n M) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (he : ∀ v w, g.inner x (e v) (e w) = inner ℝ v w) (i j : Fin n) :
    M04.frameInverseGram g x e.toContinuousLinearMap i j = if i = j then 1 else 0 := by
  change inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
    ((M04.frameGramOperator g x e.toContinuousLinearMap).inverse
      (EuclideanSpace.basisFun (Fin n) ℝ j)) = _
  rw [cap_frameGram_eq_identity g x e he, ContinuousLinearMap.inverse_id,
    ContinuousLinearMap.id_apply]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]

theorem cap_tensorNorm_frame {r : ℕ} (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M r) (x : M)
    (hT : ∃ A : MultilinearMap ℝ (fun _ : Fin r => TangentSpace (𝓡 n) x) ℝ,
      ∀ v, T x v = A v)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (he : ∀ v w, g.inner x (e v) (e w) = inner ℝ v w) :
    ‖(WithLp.toLp 2 (fun a : Fin r → Fin n =>
      T x (fun j => e (EuclideanSpace.basisFun (Fin n) ℝ (a j)))) :
      EuclideanSpace ℝ (Fin r → Fin n))‖ = g.tensorNorm T x := by
  classical
  have hprod (a b : Fin r → Fin n) :
      (∏ j : Fin r, if a j = b j then (1 : ℝ) else 0) = if a = b then 1 else 0 := by
    by_cases hab : a = b
    · subst b
      simp
    · rw [if_neg hab]
      obtain ⟨j, hj⟩ := not_forall.mp (fun h => hab (funext h))
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  have hN : 0 ≤ g.tensorNorm T x := Real.sqrt_nonneg _
  apply (sq_eq_sq₀ (norm_nonneg _) hN).mp
  rw [cap_array_norm_sq, M04.tensorNorm_sq_eq_inverseGram g T x hT e]
  symm
  apply Finset.sum_congr rfl
  intro a _
  simp only [cap_frameInverseGram_eq_ite g x e he, hprod, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, pow_two]

theorem cap_tensorNorm_frame_pair (g : RiemannianMetric n M)
    (T : CovariantTensorEvaluation n M 2) (x : M)
    (hT : ∃ A : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 n) x) ℝ,
      ∀ v, T x v = A v)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (he : ∀ v w, g.inner x (e v) (e w) = inner ℝ v w) :
    ‖(WithLp.toLp 2 (fun p : Fin n × Fin n =>
      T x ![e (EuclideanSpace.basisFun (Fin n) ℝ p.1),
        e (EuclideanSpace.basisFun (Fin n) ℝ p.2)]) :
      EuclideanSpace ℝ (Fin n × Fin n))‖ = g.tensorNorm T x := by
  have h := cap_array_norm_reindex (finTwoArrowEquiv (Fin n)).symm
    (fun a : Fin 2 → Fin n => T x (fun j => e (EuclideanSpace.basisFun (Fin n) ℝ (a j))))
  refine Eq.trans ?_ (h.trans (cap_tensorNorm_frame g T x hT e he))
  apply congrArg (fun f : Fin n × Fin n → ℝ =>
    ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin n × Fin n))‖)
  funext p
  apply congrArg (T x)
  funext j
  fin_cases j <;> rfl

theorem cap_tensorNorm_frame_triple
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (T : CovariantTensorEvaluation 3 M 3) (x : M)
    (hT : ∃ A : MultilinearMap ℝ (fun _ : Fin 3 => TangentSpace (𝓡 3) x) ℝ,
      ∀ v, T x v = A v)
    (e : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] TangentSpace (𝓡 3) x)
    (he : ∀ v w, g.inner x (e v) (e w) = inner ℝ v w) :
    ‖capThreeTensorComponents (fun i j k => T x
      ![e (EuclideanSpace.basisFun (Fin 3) ℝ i), e (EuclideanSpace.basisFun (Fin 3) ℝ j),
        e (EuclideanSpace.basisFun (Fin 3) ℝ k)])‖ = g.tensorNorm T x := by
  let f : (Fin 3 × (Fin 3 × Fin 3)) ≃ (Fin 3 → Fin 3) :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2]
      invFun := fun a => (a 0, a 1, a 2)
      left_inv := fun _ => rfl
      right_inv := by intro a; funext j; fin_cases j <;> rfl }
  have h := cap_array_norm_reindex f
    (fun a : Fin 3 → Fin 3 => T x (fun j => e (EuclideanSpace.basisFun (Fin 3) ℝ (a j))))
  refine Eq.trans ?_ (h.trans (cap_tensorNorm_frame g T x hT e he))
  apply congrArg (fun f : Fin 3 × (Fin 3 × Fin 3) → ℝ =>
    ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (Fin 3 × (Fin 3 × Fin 3)))‖)
  funext p
  apply congrArg (T x)
  funext j
  fin_cases j <;> rfl

end PoincareConjecture.M47
