import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic



open Set
namespace Poincare.CurvatureIntegral
theorem exists_normalized_strip_centers :
    ∃ T : Finset (Icc (7 / 12 : ℝ) (3 / 5)),
      ∀ τ r v : ℝ, 0 < τ → 0 < r →
        v / (2 * τ * r) ∈ Icc (7 / 12 : ℝ) (3 / 5) →
        ∃ t ∈ T, |v - 2 * τ * ((t : ℝ) * r)| ≤ (τ * r / 1024) / 128 := by
  classical
  obtain ⟨T, hT⟩ := isCompact_Icc.elim_finite_subcover
    (fun t : Icc (7 / 12 : ℝ) (3 / 5) => Metric.ball (t : ℝ) (1 / 262144))
    (fun _ => Metric.isOpen_ball)
    (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simp⟩)
  refine ⟨T, ?_⟩
  intro τ r v hτ hr hv
  obtain ⟨t, ht, hdist⟩ := mem_iUnion₂.mp (hT hv)
  rw [Metric.mem_ball, Real.dist_eq] at hdist
  refine ⟨t, ht, ?_⟩
  have heq : v - 2 * τ * ((t : ℝ) * r) =
      (2 * τ * r) * (v / (2 * τ * r) - (t : ℝ)) := by field_simp
  rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 2 * τ * r)]
  have hh := mul_le_mul_of_nonneg_left hdist.le (by positivity : 0 ≤ 2 * τ * r)
  nlinarith

noncomputable def normalizedStripCenters : Finset (Icc (7 / 12 : ℝ) (3 / 5)) :=
  Classical.choose exists_normalized_strip_centers

theorem normalizedStripCenters_cover (τ r v : ℝ) (hτ : 0 < τ) (hr : 0 < r)
    (hv : v / (2 * τ * r) ∈ Icc (7 / 12 : ℝ) (3 / 5)) :
    ∃ t ∈ normalizedStripCenters,
      |v - 2 * τ * ((t : ℝ) * r)| ≤ (τ * r / 1024) / 128 :=
  Classical.choose_spec exists_normalized_strip_centers τ r v hτ hr hv

theorem normalized_radial_value_mem_cover_interval {τ r d v : ℝ}
    (hτ : 0 < τ) (hr : 0 < r)
    (hd : d ∈ Icc (113 * r / 96) (19 * r / 16))
    (hv : |v - τ * d| ≤ τ * (r / 65536)) :
    v / (2 * τ * r) ∈ Icc (7 / 12 : ℝ) (3 / 5) := by
  have hden : 0 < 2 * τ * r := by positivity
  have hlo := mul_le_mul_of_nonneg_left hd.1 hτ.le
  have hhi := mul_le_mul_of_nonneg_left hd.2 hτ.le
  rcases abs_le.mp hv with ⟨hl, hu⟩
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith
end Poincare.CurvatureIntegral
