import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Scalar











set_option autoImplicit false
open Set
open scoped Manifold ContDiff Bundle ENNReal
universe u

namespace PoincareConjecture.RicciFlow

theorem rescalingTime_mem_Icc {Q : ℝ} (hQ : 0 < Q) (τ A : ℝ)
    {s : ℝ} (hs : s ∈ Icc (-A) 0) : τ + s / Q ∈ Icc (τ - A / Q) τ := by
  constructor
  · have h := div_le_div_of_nonneg_right hs.1 hQ.le
    rw [neg_div] at h
    linarith
  · have h := div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le
    linarith

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}


noncomputable def normalizedCylinder (F : RicciFlow n M J)
    (Q : ℝ) (hQ : 0 < Q) (τ A : ℝ) (hA : 0 < A)
    (hJ : Icc (τ - A / Q) τ ⊆ J) : RicciFlow n M (Icc (-A) 0) :=
  F.parabolicRescale Q hQ τ
    (fun _ hs ↦ hJ (rescalingTime_mem_Icc hQ τ A hs)) ordConnected_Icc
    ⟨-A, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩

theorem normalizedCylinder_metric (F : RicciFlow n M J)
    (Q : ℝ) (hQ : 0 < Q) (τ A : ℝ) (hA : 0 < A)
    (hJ : Icc (τ - A / Q) τ ⊆ J) (s : ℝ) :
    (F.normalizedCylinder Q hQ τ A hA hJ).metric s =
      rescaledMetric (F.metric (τ + s / Q)) Q hQ := rfl

theorem normalizedCylinder_scalar_zero (F : RicciFlow n M J)
    (Q : ℝ) (hQ : 0 < Q) (τ A : ℝ) (hA : 0 < A)
    (hJ : Icc (τ - A / Q) τ ⊆ J) (y : M)
    (hbase : (F.connection τ).scalarCurvature y = Q) :
    ((F.normalizedCylinder Q hQ τ A hA hJ).connection 0).scalarCurvature y = 1 := by
  change (rescaledMetric_connection _ _ Q hQ).scalarCurvature y = 1
  rw [rescaledMetric_scalarCurvature, zero_div, add_zero, hbase, inv_mul_cancel₀ hQ.ne']

theorem normalizedCylinder_scalar_le_four (F : RicciFlow n M J)
    (Q : ℝ) (hQ : 0 < Q) (τ A : ℝ) (hA : 0 < A)
    (hJ : Icc (τ - A / Q) τ ⊆ J) (y : M) (B : ℝ)
    (hbound : ∀ t ∈ Icc (τ - A / Q) τ, ∀ z : M,
      (F.metric τ).edist y z ≤ ENNReal.ofReal (B / Real.sqrt Q) →
        (F.connection t).scalarCurvature z ≤ 4 * Q) :
    ∀ s ∈ Icc (-A) 0, ∀ z : M,
      ((F.normalizedCylinder Q hQ τ A hA hJ).metric 0).edist y z ≤
        ENNReal.ofReal B →
      ((F.normalizedCylinder Q hQ τ A hA hJ).connection s).scalarCurvature z ≤ 4 := by
  intro s hs z hz
  have hsq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hne : ENNReal.ofReal (Real.sqrt Q) ≠ 0 := (ENNReal.ofReal_pos.mpr hsq).ne'
  change (rescaledMetric _ Q hQ).edist y z ≤ ENNReal.ofReal B at hz
  rw [rescaledMetric_edist, zero_div, add_zero] at hz
  have hz' : (F.metric τ).edist y z ≤ ENNReal.ofReal (B / Real.sqrt Q) := by
    rw [ENNReal.ofReal_div_of_pos hsq,
      ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hz
  have h := hbound (τ + s / Q) (rescalingTime_mem_Icc hQ τ A hs) z hz'
  change (rescaledMetric_connection _ _ Q hQ).scalarCurvature z ≤ 4
  rw [rescaledMetric_scalarCurvature]
  calc
    Q⁻¹ * (F.connection (τ + s / Q)).scalarCurvature z ≤ Q⁻¹ * (4 * Q) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hQ.le)
    _ = 4 := by field_simp

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.RicciFlow




theorem exists_normalized_large_cylinder
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a t₀ : ℝ} (hm : 0 < m) (hJ : Icc a t₀ ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a t₀, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a t₀, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (p : M) {r A : ℝ} (hr : 0 < r) (hA : 0 < A)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a t₀) {x₁ : M}
    (hx₁ : (F.metric t₁).edist p x₁ ≤ ENNReal.ofReal (r / 4))
    (hlarge : (64 * (((m + 1 : ℕ) : ℝ) + 8) * A / r) ^ 2 <
      (F.connection t₁).scalarCurvature x₁)
    (hthreshold : 2 * A ≤ (F.connection t₁).scalarCurvature x₁ * (t₁ - a)) :
    ∃ τ ∈ Icc a t₁, ∃ y ∈ (F.metric τ).ball p (r / 2),
      ∃ Q : ℝ, ∃ hQ : 0 < Q, ∃ G : RicciFlow (m + 1) M (Icc (-A) 0),
        Q = (F.connection τ).scalarCurvature y ∧
        (F.connection t₁).scalarCurvature x₁ ≤ Q ∧
        2 * A ≤ Q * (τ - a) ∧
        (∀ s, G.metric s = rescaledMetric (F.metric (τ + s / Q)) Q hQ) ∧
        (G.connection 0).scalarCurvature y = 1 ∧
        (∀ s ∈ Icc (-A) 0, ∀ z : M,
          (G.metric 0).edist y z ≤ ENNReal.ofReal A →
          (G.connection s).scalarCurvature z ≤ 4) ∧
        (∀ s ∈ Icc (-A) 0, MetricComplete (G.metric s)) ∧
        (∀ s ∈ Icc (-A) 0, ∀ z : M,
          (G.connection s).NonnegativeCurvatureOperator z) := by
  obtain ⟨τ, hτ, y, hy, Q, hQeq, hQ, hQ₁, hQt, hbound⟩ :=
    exists_scalarCurvature_large_cylinder hC F hm hJ hcomplete hoperator p hr hA
      ht₁ hx₁ hlarge hthreshold
  have htime : A / Q ≤ τ - a := by
    apply (div_le_iff₀ hQ).mpr
    nlinarith
  have hsub : Icc (τ - A / Q) τ ⊆ Icc a t₀ :=
    Icc_subset_Icc (by linarith) (hτ.2.trans ht₁.2)
  have hdomain : Icc (τ - A / Q) τ ⊆ J := fun _ ht ↦ interior_subset (hJ (hsub ht))
  let G := F.normalizedCylinder Q hQ τ A hA hdomain
  refine ⟨τ, hτ, y, hy, Q, hQ, G, hQeq, hQ₁, hQt,
    F.normalizedCylinder_metric Q hQ τ A hA hdomain,
    F.normalizedCylinder_scalar_zero Q hQ τ A hA hdomain y hQeq.symm,
    F.normalizedCylinder_scalar_le_four Q hQ τ A hA hdomain y A hbound, ?_, ?_⟩
  · intro s hs
    exact F.parabolicRescale_metricComplete Q hQ τ _ _ _ s
      (hcomplete _ (hsub (rescalingTime_mem_Icc hQ τ A hs)))
  · intro s hs z
    exact F.parabolicRescale_nonnegativeCurvatureOperator Q hQ τ _ _ _ s z
      (hoperator _ (hsub (rescalingTime_mem_Icc hQ τ A hs)) z)

end PoincareConjecture.RicciFlow
