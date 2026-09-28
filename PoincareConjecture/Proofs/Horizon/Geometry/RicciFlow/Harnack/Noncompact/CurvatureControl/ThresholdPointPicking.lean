import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.PointPicking
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.MetricMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem exists_scalarCurvature_threshold_point_with_radius_control
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {a t₀ : ℝ} (hJ : Icc a t₀ ⊆ interior J)
    (hcomplete : MetricComplete (F.metric t₀))
    (hRic : ∀ t ∈ Icc a t₀, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    (p : M) (r : ℝ) {L α : ℝ} (hL : 0 ≤ L) (hα : 0 < α)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a t₀) {x₁ : M}
    (hx₁ : x₁ ∈ (F.metric t₁).ball p r)
    (hthreshold : α ≤ (F.connection t₁).scalarCurvature x₁ * (t₁ - a)) :
    ∃ τ ∈ Icc a t₁, ∃ y ∈ (F.metric τ).ball p r,
      ∃ Q : ℝ, Q = (F.connection τ).scalarCurvature y ∧
        0 < Q ∧ (F.connection t₁).scalarCurvature x₁ ≤ Q ∧
        α ≤ Q * (τ - a) ∧
        ((F.metric τ).edist p y).toReal + 2 * L / Real.sqrt Q ≤
          ((F.metric t₁).edist p x₁).toReal +
            2 * L / Real.sqrt ((F.connection t₁).scalarCurvature x₁) ∧
        ∀ s ∈ Icc (τ - α / (2 * Q)) τ, ∀ z ∈ (F.metric s).ball p r,
          ((F.metric s).edist p z).toReal ≤
              ((F.metric τ).edist p y).toReal + L / Real.sqrt Q →
          (F.connection s).scalarCurvature z ≤ 4 * Q := by
  let S : Set (ℝ × M) := {z | z.1 ∈ Icc a t₀ ∧
    z.2 ∈ (F.metric z.1).ball p r ∧
    α ≤ (F.connection z.1).scalarCurvature z.2 * (z.1 - a)}
  let K : Set (ℝ × M) := Icc a t₀ ×ˢ
    {x | (F.metric t₀).edist p x ≤ ENNReal.ofReal r}
  let q : ℝ × M → ℝ := fun z =>
    Real.sqrt ((F.connection z.1).scalarCurvature z.2)
  let radius : ℝ × M → ℝ := fun z =>
    ((F.metric z.1).edist p z.2).toReal
  have htop : t₀ ∈ Icc a t₀ := ⟨ht₁.1.trans ht₁.2, le_rfl⟩
  have hSK : S ⊆ K := by
    rintro ⟨s, z⟩ ⟨hs, hz, _⟩
    refine ⟨hs, ?_⟩
    have hball := F.ball_subset_ball_of_ricci_nonneg hJ p r hs htop hs.2
      (fun t ht x _ v => hRic t ht x v) hz
    exact (show (F.metric t₀).edist p z < ENNReal.ofReal r from hball).le
  have hK : IsCompact K := isCompact_Icc.prod
    ((F.metric t₀).isCompact_closedBall_of_metricComplete hcomplete p r)
  have hq : ContinuousOn q K := Real.continuous_sqrt.comp_continuousOn
    ((hC.scalar_regular n M J F).continuousOn.mono (fun z hz =>
      ⟨interior_subset (hJ hz.1), mem_univ _⟩))
  have hbound : BddAbove (q '' S) :=
    (hK.bddAbove_image hq).mono (image_mono hSK)
  have hR (s : ℝ) (hs : s ∈ Icc a t₀) (z : M) :
      0 ≤ (F.connection s).scalarCurvature z :=
    Finset.sum_nonneg (fun i _ => hRic s hs z _)
  have hR₁ : 0 < (F.connection t₁).scalarCurvature x₁ := by
    have hta : 0 < t₁ - a := by
      have hta0 : 0 ≤ t₁ - a := sub_nonneg.mpr ht₁.1
      by_contra h
      have : t₁ - a = 0 := le_antisymm (le_of_not_gt h) hta0
      rw [this, mul_zero] at hthreshold
      linarith
    have hnonneg := hR t₁ ht₁ x₁
    nlinarith
  obtain ⟨⟨τ, y⟩, hτy, htime, hqxy, hrad, hlocal⟩ :=
    Poincare.Parabolic.exists_point_with_doubling_bound S q radius Prod.fst
      hbound hL
      (show (t₁, x₁) ∈ S from ⟨ht₁, hx₁, hthreshold⟩)
      (Real.sqrt_pos.mpr hR₁)
  have hτ : τ ∈ Icc a t₁ := ⟨hτy.1.1, htime⟩
  have hτ₀ : τ ∈ Icc a t₀ := hτy.1
  have hy : y ∈ (F.metric τ).ball p r := hτy.2.1
  have hτthreshold : α ≤
      (F.connection τ).scalarCurvature y * (τ - a) := hτy.2.2
  let Q : ℝ := (F.connection τ).scalarCurvature y
  have hq₁ : 0 < q (t₁, x₁) := by
    dsimp only [q]
    exact Real.sqrt_pos.mpr hR₁
  have hqτ : 0 < q (τ, y) := lt_of_lt_of_le hq₁ hqxy
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact Real.sqrt_pos.mp hqτ
  have hQthreshold : α ≤ Q * (τ - a) := by
    simpa only [Q] using hτthreshold
  have hτa : a < τ := by
    have hprod : 0 < Q * (τ - a) := hα.trans_le hQthreshold
    nlinarith [hprod]
  have hfrac : α / (2 * Q) ≤ (τ - a) / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) * Q)).2
    nlinarith [hQthreshold]
  have hbase : a ≤ τ - α / (2 * Q) := by linarith
  have hQ₁ : (F.connection t₁).scalarCurvature x₁ ≤ Q := by
    have hsquare := mul_self_le_mul_self (Real.sqrt_nonneg
      ((F.connection t₁).scalarCurvature x₁)) hqxy
    dsimp only [q] at hsquare
    nlinarith [Real.sq_sqrt hR₁.le, Real.sq_sqrt hQ.le]
  refine ⟨τ, hτ, y, hy, Q, rfl, hQ, hQ₁, hQthreshold, hrad, ?_⟩
  intro s hs z hz hdist
  have hsτ : s ≤ τ := hs.2
  have hsa : a ≤ s := hbase.trans hs.1
  have hsall : s ∈ Icc a t₀ :=
    ⟨hsa, hsτ.trans hτ₀.2⟩
  have hthreshold_or :
      α ≤ (F.connection s).scalarCurvature z * (s - a) ∨
        (F.connection s).scalarCurvature z * (s - a) < α :=
    by
      rcases lt_or_ge ((F.connection s).scalarCurvature z * (s - a)) α with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases hthreshold_or with hthreshold_z | hbelow
  · have hdist' : radius (s, z) ≤ radius (τ, y) + L / q (τ, y) := by
      simpa only [radius, q, Q] using hdist
    have hlocal' := hlocal (s, z) ⟨hsall, hz, hthreshold_z⟩ hsτ hdist'
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg
      ((F.connection s).scalarCurvature z)) hlocal'
    dsimp only [q, Q] at hsq ⊢
    nlinarith [Real.sq_sqrt (hR s hsall z), Real.sq_sqrt (hR τ hτy.1 y)]
  · have hsa_pos : 0 < s - a := by
      have hbound_s : α / (2 * Q) ≤ s - a := by linarith [hs.1]
      have : 0 < α / (2 * Q) := by positivity
      exact this.trans_le hbound_s
    have hαupper : α ≤ 2 * Q * (s - a) := by
      have hbound_s : α / (2 * Q) ≤ s - a := by linarith [hs.1]
      have hmul := (div_le_iff₀ (by positivity : 0 < (2 : ℝ) * Q)).mp hbound_s
      nlinarith [hmul]
    have hlt : (F.connection s).scalarCurvature z * (s - a) <
        (2 * Q) * (s - a) := hbelow.trans_le hαupper
    have hRlt : (F.connection s).scalarCurvature z < 2 * Q := by
      by_contra hnot
      have hle : 2 * Q ≤ (F.connection s).scalarCurvature z := le_of_not_gt hnot
      have hmul := mul_le_mul_of_nonneg_right hle hsa_pos.le
      linarith
    linarith

theorem exists_scalarCurvature_threshold_point
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {a t₀ : ℝ} (hJ : Icc a t₀ ⊆ interior J)
    (hcomplete : MetricComplete (F.metric t₀))
    (hRic : ∀ t ∈ Icc a t₀, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    (p : M) (r : ℝ) {L α : ℝ} (hL : 0 ≤ L) (hα : 0 < α)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc a t₀) {x₁ : M}
    (hx₁ : x₁ ∈ (F.metric t₁).ball p r)
    (hthreshold : α ≤ (F.connection t₁).scalarCurvature x₁ * (t₁ - a)) :
    ∃ τ ∈ Icc a t₁, ∃ y ∈ (F.metric τ).ball p r,
      ∃ Q : ℝ, Q = (F.connection τ).scalarCurvature y ∧
        0 < Q ∧ α ≤ Q * (τ - a) ∧
        ∀ s ∈ Icc (τ - α / (2 * Q)) τ, ∀ z ∈ (F.metric s).ball p r,
          ((F.metric s).edist p z).toReal ≤
              ((F.metric τ).edist p y).toReal + L / Real.sqrt Q →
          (F.connection s).scalarCurvature z ≤ 4 * Q := by
  obtain ⟨τ, hτ, y, hy, Q, heq, hQ, _, hthreshold, _, hbound⟩ :=
    exists_scalarCurvature_threshold_point_with_radius_control hC F hJ hcomplete
      hRic p r hL hα ht₁ hx₁ hthreshold
  exact ⟨τ, hτ, y, hy, Q, heq, hQ, hthreshold, hbound⟩

end PoincareConjecture.RicciFlow
