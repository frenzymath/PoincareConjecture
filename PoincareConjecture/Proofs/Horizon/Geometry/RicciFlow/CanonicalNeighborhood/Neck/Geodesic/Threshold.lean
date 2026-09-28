import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Long
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Pairing

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

theorem scaled_long_neck_window_identity {r ε K C : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    r * ((r * Real.sqrt (1 + ε))⁻¹ - C / (r / (200 * Real.sqrt ε)) -
      (K * ε / r ^ 2) * (r / (200 * Real.sqrt ε))) =
      (Real.sqrt (1 + ε))⁻¹ - (200 * C + K / 200) * Real.sqrt ε := by
  have hs : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.mpr hε).ne'
  have hs₁ : Real.sqrt (1 + ε) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  have heq := Real.sq_sqrt hε.le
  field_simp [hr.ne', hs, hs₁]
  linear_combination (Real.sqrt (1 + ε) * K) * heq

theorem exists_long_neck_window_threshold (K C : ℝ) {β : ℝ} (hβ : 0 < β) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 2 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ r : ℝ, 0 < r →
        0 < (r * Real.sqrt (1 + ε))⁻¹ - C / (r / (200 * Real.sqrt ε)) -
          (K * ε / r ^ 2) * (r / (200 * Real.sqrt ε)) ∧
        1 - β ≤ r * ((r * Real.sqrt (1 + ε))⁻¹ -
          C / (r / (200 * Real.sqrt ε)) -
          (K * ε / r ^ 2) * (r / (200 * Real.sqrt ε))) := by
  let F : ℝ → ℝ := fun ε =>
    (Real.sqrt (1 + ε))⁻¹ - (200 * C + K / 200) * Real.sqrt ε
  have hF : ContinuousAt F 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.inv₀
      · fun_prop
      · norm_num
    · fun_prop
  have hF0 : F 0 = 1 := by norm_num [F]
  have htol : 0 < min β (1 / 2) := lt_min hβ (by norm_num)
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hF (min β (1 / 2)) htol
  refine ⟨min (δ / 2) (1 / 4), lt_min (by positivity) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro ε hε hε₀ r hr
  have hεδ : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]
    have h := hε₀.trans (min_le_left _ _)
    linarith
  have hclose := hnear hεδ
  rw [hF0, Real.dist_eq] at hclose
  have hlo := (abs_lt.mp hclose).1
  have hpos : 0 < F ε := by
    have hhalf := min_le_right β (1 / 2)
    linarith
  have hquality : 1 - β ≤ F ε := by
    have hbeta := min_le_left β (1 / 2)
    linarith
  have heq := scaled_long_neck_window_identity (K := K) (C := C) hr hε
  change _ = F ε at heq
  constructor
  · have hmul : 0 < r * ((r * Real.sqrt (1 + ε))⁻¹ -
        C / (r / (200 * Real.sqrt ε)) -
        (K * ε / r ^ 2) * (r / (200 * Real.sqrt ε))) := by
      rw [heq]
      exact hpos
    exact pos_of_mul_pos_right hmul hr.le
  · rwa [heq]

theorem exists_axial_alignment_window_threshold (K C : ℝ) {α : ℝ} (hα : 0 < α) :
    ∃ β ε₀ : ℝ, 0 < β ∧ 0 < ε₀ ∧ ε₀ < 1 / 2 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ r : ℝ, 0 < r →
        0 < (r * Real.sqrt (1 + ε))⁻¹ - C / (r / (200 * Real.sqrt ε)) -
          (K * ε / r ^ 2) * (r / (200 * Real.sqrt ε)) ∧
        1 - β ≤ r * ((r * Real.sqrt (1 + ε))⁻¹ -
          C / (r / (200 * Real.sqrt ε)) -
          (K * ε / r ^ 2) * (r / (200 * Real.sqrt ε))) ∧
        2 * β + 5 * ε < α ^ 2 := by
  let β : ℝ := min (α ^ 2 / 8) (1 / 4)
  have hβ : 0 < β := lt_min (by positivity) (by norm_num)
  obtain ⟨δ, hδ, hδhalf, hwindow⟩ := exists_long_neck_window_threshold K C hβ
  refine ⟨β, min δ (α ^ 2 / 20), hβ, lt_min hδ (by positivity),
    lt_of_le_of_lt (min_le_left _ _) hδhalf, ?_⟩
  intro ε hε hε₀ r hr
  have h := hwindow ε hε (hε₀.trans (min_le_left _ _)) r hr
  refine ⟨h.1, h.2, ?_⟩
  have hβbound : β ≤ α ^ 2 / 8 := min_le_left _ _
  have hεbound := hε₀.trans (min_le_right _ _)
  nlinarith [sq_pos_of_pos hα]

theorem exists_intrinsic_neck_alignment_threshold
    (K C : ℝ) (hC : 0 ≤ C) {α : ℝ} (hα : 0 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g),
        N.epsilon ≤ ε₀ → ∀ {γ : ℝ → M} {acc : ℝ → ℝ} {L : ℝ},
        let f : ℝ → ℝ := fun t => (N.coordinate_inverse (γ t)).2
        let v : ℝ → ℝ := fun t =>
          mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) (γ t)
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
        N.scale / (100 * N.epsilon) < L →
        (∀ t ∈ Icc 0 L, γ t ∈ N.carrier) →
        (∀ t ∈ Icc 0 L,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1) →
        (∀ t ∈ Icc 0 L, HasDerivAt f (v t) t) →
        (∀ t ∈ Icc 0 L, HasDerivAt v (acc t) t) →
        (∀ t ∈ Icc 0 L, |acc t| ≤ K * N.epsilon / N.scale ^ 2) →
        (∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
          a ≤ b → ENNReal.ofReal (b - a) ≤ intrinsicEDist g N.carrier (γ a) (γ b)) →
        (∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
          a ≤ b → intrinsicEDist g N.carrier (γ a) (γ b) ≤
            ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * (|f b - f a| + C))) →
        f 0 < f L → ∀ t ∈ Icc 0 L,
        let a : TangentSpace (𝓡 3) (γ t) := N.scale⁻¹ •
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
            N.coordinate_map (N.coordinate_inverse (γ t)) (0, 1)
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1 - a) < α := by
  obtain ⟨β, ε₀, _, hε₀, _, hwindow⟩ :=
    exists_axial_alignment_window_threshold K C (half_pos hα)
  refine ⟨ε₀, hε₀, ?_⟩
  intro M _ _ _ _ _ _ _ g N hN γ acc L
  dsimp only
  intro hL hcarrier hunit hf hv hacc hsegment hcompetitor horient t ht
  have h := hwindow N.epsilon N.epsilon_pos hN N.scale N.scale_pos
  have hvel := N.long_neck_axial_speed_of_intrinsic_minimality hL h.1 h.2.1
    hf hv hacc hC hsegment hcompetitor horient
  exact (N.tangentNorm_sub_scaled_axial_le_of_velocity (hcarrier t ht)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) (hunit t ht) (half_pos hα).le
    (hvel t ht) h.2.2.le).trans_lt (half_lt_self hα)

end PoincareConjecture.EpsilonNeck
