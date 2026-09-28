import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.ScalarTime










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

theorem PoincareConjecture.RicciFlow.exists_terminal_scalar_positive_time_buffer
    {m : ℕ} (hC : PoincareConjecture.RicciFlowCurvatureTheory.{u}) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M] (J : Set ℝ)
        (F : PoincareConjecture.RicciFlow (m + 1) M J),
        Icc (-2 : ℝ) 0 ⊆ interior J →
        (∀ t ∈ Icc (-2 : ℝ) 0, PoincareConjecture.MetricComplete (F.metric t)) →
        (∀ t ∈ Icc (-2 : ℝ) 0, ∀ x : M,
          (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M,
          (∀ t ∈ Icc (-2 : ℝ) 0,
            ∀ x ∈ (F.metric 0).ball p (64 * (((m + 1 : ℕ) : ℝ) + 8)),
              (F.connection t).scalarCurvature x ≤ 4) →
          (F.connection 0).scalarCurvature p = 1 →
          ∀ t ∈ Icc (-δ) 0, (1 : ℝ) / 2 ≤ (F.connection t).scalarCurvature p := by
  obtain ⟨D, hD, htime⟩ := exists_terminal_scalar_time_constant hC hm
  let δ := min (1 / 2 : ℝ) (1 / (2 * D))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδD : D * δ ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * D)).mp
      (show δ ≤ 1 / (2 * D) from min_le_right _ _)
    nlinarith
  refine ⟨δ, hδ, by linarith, ?_⟩
  intro M _ _ _ _ _ J F hJ hcomplete hoperator p hscalar hnormalize t ht
  have ht' : t ∈ Icc (-1 : ℝ) 0 := ⟨by linarith [ht.1], ht.2⟩
  have hcompare := htime M J F hJ hcomplete hoperator p hscalar t ht'
  rw [hnormalize] at hcompare
  have htime' : D * (0 - t) ≤ D * δ :=
    mul_le_mul_of_nonneg_left (by linarith [ht.1]) hD.le
  linarith
