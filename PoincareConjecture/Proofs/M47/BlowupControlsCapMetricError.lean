import PoincareConjecture.Proofs.M47.BlowupControlsCapInverseMetric










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem cap_metricDifference_smooth (g0 g1 : RiemannianMetric n M) :
    IsSmoothCovariantTensor
      (fun x (v : Fin 2 → TangentSpace (𝓡 n) x) =>
        g1.inner x (v 0) (v 1) - g0.inner x (v 0) (v 1)) := by
  classical
  constructor
  · intro x
    refine ⟨MultilinearMap.mk' (R := ℝ)
      (fun v : Fin 2 → TangentSpace (𝓡 n) x =>
        g1.inner x (v 0) (v 1) - g0.inner x (v 0) (v 1)) ?_ ?_, fun _ => rfl⟩
    · intro v i a b
      fin_cases i <;>
        simp [Function.update, map_add, add_apply] <;> ring
    · intro v i r a
      fin_cases i <;>
        simp [Function.update, map_smul, smul_apply, smul_eq_mul] <;> ring
  · intro U _ X hX
    have hmetric (g : RiemannianMetric n M) :
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
          (fun x => g.inner x (X 0 x) (X 1 x)) U := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact (hX 0).inner_bundle (hX 1)
    exact (hmetric g1).sub (hmetric g0)

set_option backward.isDefEq.respectTransparency false in


theorem cap_metricDifference_quadratic_le (g0 g1 : RiemannianMetric n M)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    |g1.inner x v v - g0.inner x v v| ≤
      g0.tensorNorm (fun y (w : Fin 2 → TangentSpace (𝓡 n) y) =>
        g1.inner y (w 0) (w 1) - g0.inner y (w 0) (w 1)) x * g0.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g0.toRiemannianMetric⟩
  let H : CovariantTensorEvaluation n M 2 :=
    fun y w => g1.inner y (w 0) (w 1) - g0.inner y (w 0) (w 1)
  have hb := M04.tensorEvaluation_sq_le_tensorNorm g0
    (cap_metricDifference_smooth g0 g1) x ![v, v]
  change _ ≤ g0.tensorNorm H x * g0.inner x v v
  have hN : 0 ≤ g0.tensorNorm H x := Real.sqrt_nonneg _
  have hV : 0 ≤ g0.inner x v v := real_inner_self_nonneg (x := v)
  have hs : (g1.inner x v v - g0.inner x v v) ^ 2 ≤
      (g0.tensorNorm H x * g0.inner x v v) ^ 2 := by
    simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      ← pow_two, mul_pow] using hb
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hN hV)).mp (by rwa [sq_abs])



theorem cap_metricDifference_frame_lower (g0 g1 : RiemannianMetric n M)
    (x : M) (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (he : ∀ v w, g0.inner x (e v) (e w) = inner ℝ v w)
    {gamma : ℝ}
    (herror : g0.tensorNorm (fun y (w : Fin 2 → TangentSpace (𝓡 n) y) =>
        g1.inner y (w 0) (w 1) - g0.inner y (w 0) (w 1)) x ≤ gamma)
    (v : EuclideanSpace ℝ (Fin n)) :
    (1 - gamma) * ‖v‖ ^ 2 ≤ g1.inner x (e v) (e v) := by
  have h := cap_metricDifference_quadratic_le g0 g1 x (e v)
  rw [he, real_inner_self_eq_norm_sq] at h
  have hmul := mul_le_mul_of_nonneg_right herror (sq_nonneg ‖v‖)
  have hlo := neg_abs_le (g1.inner x (e v) (e v) - ‖v‖ ^ 2)
  linarith



theorem cap_metricDifference_inverse_norm_le (g0 g1 : RiemannianMetric n M)
    (x : M) (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (he : ∀ v w, g0.inner x (e v) (e w) = inner ℝ v w)
    {gamma : ℝ} (hgamma : gamma < 1)
    (herror : g0.tensorNorm (fun y (w : Fin 2 → TangentSpace (𝓡 n) y) =>
        g1.inner y (w 0) (w 1) - g0.inner y (w 0) (w 1)) x ≤ gamma) :
    ‖(M04.frameGramOperator g1 x e.toContinuousLinearMap).inverse‖ ≤
      (1 - gamma)⁻¹ :=
  cap_frameInverseGram_norm_le g1 x e hgamma
    (cap_metricDifference_frame_lower g0 g1 x e he herror)

end PoincareConjecture.M47
