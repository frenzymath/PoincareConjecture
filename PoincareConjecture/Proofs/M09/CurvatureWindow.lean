import PoincareConjecture.Proofs.M09.TensorEvaluationBound








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem ricci_abs_le_of_curvature_bound (hM04 : RicciFlowCurvatureTheory.{u})
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) (K : ℝ) (hK : D.curvatureTensorNorm x ≤ K) :
    |D.ricci x v w| ≤ (n : ℝ) * K * g.tangentNorm x v * g.tangentNorm x w := by
  apply (ricci_abs_le_curvatureTensorNorm hM04 g D x v w).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg n))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

theorem scalar_abs_le_of_curvature_bound (hM04 : RicciFlowCurvatureTheory.{u})
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (x : M)
    (K : ℝ) (hK : D.curvatureTensorNorm x ≤ K) :
    |D.scalarCurvature x| ≤ (n : ℝ) ^ 2 * K :=
  (scalar_abs_le_curvatureTensorNorm hM04 g D x).trans
    (mul_le_mul_of_nonneg_left hK (sq_nonneg _))

theorem ricci_quadratic_abs_le_of_curvature_bound (hM04 : RicciFlowCurvatureTheory.{u})
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (x : M)
    (v : TangentSpace (𝓡 n) x) (K : ℝ) (hK : D.curvatureTensorNorm x ≤ K) :
    |D.ricci x v v| ≤ (n : ℝ) * K * g.inner x v v := by
  have hpos : 0 ≤ g.inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (g.pos x v hv).le
  have hn : (g.tangentNorm x v) ^ 2 = g.inner x v v := Real.sq_sqrt hpos
  calc
    _ ≤ (n : ℝ) * K * g.tangentNorm x v * g.tangentNorm x v :=
      ricci_abs_le_of_curvature_bound hM04 g D x v v K hK
    _ = _ := by rw [← hn]; ring

theorem window_metric_comparison {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b K : ℝ)
    (hb : 0 ≤ b) (hK : 0 ≤ K) (hwindow : Set.Icc (T - b) T ⊆ J)
    (hbound : ∀ s ∈ Set.Icc (T - b) T, ∀ x : M,
      (F.connection s).curvatureTensorNorm x ≤ K)
    (t : ℝ) (ht : t ∈ Set.Icc (T - b) T)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    Real.exp (-(2 * (n : ℝ) * K * b)) * (F.metric T).inner x v v ≤
        (F.metric t).inner x v v ∧
      (F.metric t).inner x v v ≤
        Real.exp (2 * (n : ℝ) * K * b) * (F.metric T).inner x v v := by
  let c : ℝ := 2 * (n : ℝ) * K
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hg (r : ℝ) : 0 ≤ (F.metric r).inner x v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact ((F.metric r).pos x v hv).le
  have hcompare := hM04.metric_comparison n M J F t T K (hwindow ht)
    (hwindow ⟨by linarith, le_rfl⟩) ht.2 hK
    (fun s hs y ↦ hbound s ⟨ht.1.trans hs.1, hs.2⟩ y) x v
  have hm : Real.exp (-(c * (T - t))) * (F.metric t).inner x v v ≤
        (F.metric T).inner x v v ∧
      (F.metric T).inner x v v ≤ Real.exp (c * (T - t)) * (F.metric t).inner x v v := by
    simpa [c, neg_mul] using hcompare
  have hlo : Real.exp (-(c * (T - t))) * (F.metric T).inner x v v ≤
      (F.metric t).inner x v v := by
    calc
      _ ≤ Real.exp (-(c * (T - t))) *
          (Real.exp (c * (T - t)) * (F.metric t).inner x v v) :=
        mul_le_mul_of_nonneg_left hm.2 (Real.exp_nonneg _)
      _ = _ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hhi : (F.metric t).inner x v v ≤
      Real.exp (c * (T - t)) * (F.metric T).inner x v v := by
    calc
      _ = Real.exp (c * (T - t)) *
          (Real.exp (-(c * (T - t))) * (F.metric t).inner x v v) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm.1 (Real.exp_nonneg _)
  have hcb : c * (T - t) ≤ c * b := mul_le_mul_of_nonneg_left (by linarith [ht.1]) hc
  refine ⟨?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcb)) (hg T)).trans hlo
  · exact hhi.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcb) (hg T))

end PoincareConjecture.Proofs.M09
