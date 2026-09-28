import PoincareConjecture.Proofs.M04.ShiPiecewiseEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pathELength_eq_integral_fixed_segment_speed (g : RiemannianMetric n M)
    {γ : ℝ → M} {a b c d : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    g.pathELength γ c d =
      ENNReal.ofReal (∫ t in c..d, M04.segmentPathSpeed g γ a b t) := by
  rcases hcd.eq_or_lt with rfl | hcd
  · simp [RiemannianMetric.pathELength]
  rw [M04.pathELength_eq_ofReal_integral_segmentPathSpeed g
    (hγ.mono (Icc_subset_Icc hac hdb)) hcd]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le hcd.le
  intro t ht
  simp only [M04.segmentPathSpeed,
    mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2),
    mfderivWithin_of_mem_nhds (Icc_mem_nhds (hac.trans_lt ht.1) (ht.2.trans_le hdb))]

theorem continuousOn_pathELength_left (g : RiemannianMetric n M)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b)) :
    ContinuousOn (fun t => g.pathELength γ t b) (Icc a b) := by
  have hint : IntegrableOn (M04.segmentPathSpeed g γ a b) (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact (M04.continuousOn_segmentPathSpeed g hγ hab).integrableOn_Icc
  have hcont := ENNReal.continuous_ofReal.comp_continuousOn
    (intervalIntegral.continuousOn_primitive_interval_left hint)
  rw [uIcc_of_le hab.le] at hcont
  apply hcont.congr
  intro t ht
  exact pathELength_eq_integral_fixed_segment_speed g hγ ht.1 ht.2 le_rfl

theorem continuousOn_pathELength_right (g : RiemannianMetric n M)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b)) :
    ContinuousOn (fun t => g.pathELength γ a t) (Icc a b) := by
  have hint : IntegrableOn (M04.segmentPathSpeed g γ a b) (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact (M04.continuousOn_segmentPathSpeed g hγ hab).integrableOn_Icc
  have hcont := ENNReal.continuous_ofReal.comp_continuousOn
    (intervalIntegral.continuousOn_primitive_interval hint)
  rw [uIcc_of_le hab.le] at hcont
  apply hcont.congr
  intro t ht
  exact pathELength_eq_integral_fixed_segment_speed g hγ le_rfl ht.1 ht.2

theorem exists_pathELength_left_anchor (g : RiemannianMetric n M)
    {γ : ℝ → M} {a b L : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (hL : 0 < L) (hroom : ENNReal.ofReal L < g.pathELength γ a b) :
    ∃ t ∈ Ioo a b, g.pathELength γ t b = ENNReal.ofReal L := by
  have hzero : g.pathELength γ b b = 0 := by
    simp [RiemannianMetric.pathELength]
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hab.le
    (continuousOn_pathELength_left g hab hγ)
    (show ENNReal.ofReal L ∈ Icc (g.pathELength γ b b) (g.pathELength γ a b) by
      rw [hzero]
      exact ⟨bot_le, hroom.le⟩)
  change g.pathELength γ t b = ENNReal.ofReal L at heq
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, heq⟩
  · intro h
    subst t
    exact (ne_of_lt hroom) heq.symm
  · intro h
    subst t
    rw [hzero] at heq
    exact (ENNReal.ofReal_pos.mpr hL).ne' heq.symm

theorem exists_pathELength_right_anchor (g : RiemannianMetric n M)
    {γ : ℝ → M} {a b L : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (hL : 0 < L) (hroom : ENNReal.ofReal L < g.pathELength γ a b) :
    ∃ t ∈ Ioo a b, g.pathELength γ a t = ENNReal.ofReal L := by
  have hzero : g.pathELength γ a a = 0 := by
    simp [RiemannianMetric.pathELength]
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hab.le
    (continuousOn_pathELength_right g hab hγ)
    (show ENNReal.ofReal L ∈ Icc (g.pathELength γ a a) (g.pathELength γ a b) by
      rw [hzero]
      exact ⟨bot_le, hroom.le⟩)
  change g.pathELength γ a t = ENNReal.ofReal L at heq
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, heq⟩
  · intro h
    subst t
    rw [hzero] at heq
    exact (ENNReal.ofReal_pos.mpr hL).ne' heq.symm
  · intro h
    subst t
    exact (ne_of_lt hroom) heq.symm

end PoincareConjecture.M28
