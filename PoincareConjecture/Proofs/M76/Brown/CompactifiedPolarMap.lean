import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Bounded












set_option autoImplicit false

open Set Metric Filter
open scoped Topology OnePoint

namespace BrownSchoenflies


noncomputable def polarRadius (t : ℝ) : ℝ := (1 + t) / (1 - t)


theorem polarRadius_nonneg {t : ℝ} (ht : -1 ≤ t) (ht' : t < 1) :
    0 ≤ polarRadius t :=
  div_nonneg (by linarith) (sub_pos.mpr ht').le

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


noncomputable def compactifiedPolar (z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1) :
    OnePoint E :=
  if (z.2 : ℝ) = 1 then ∞ else ((polarRadius z.2) • (z.1 : E) : E)


theorem norm_polarVector (z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1)
    (hz : (z.2 : ℝ) < 1) :
    ‖(polarRadius z.2) • (z.1 : E)‖ = polarRadius z.2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (polarRadius_nonneg z.2.property.1 hz),
    mem_sphere_zero_iff_norm.mp z.1.property, mul_one]





theorem continuous_compactifiedPolar :
    Continuous (compactifiedPolar : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 → OnePoint E) := by
  have ht : Continuous (fun z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 => (z.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hu : Continuous (fun z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 => (z.1 : E)) :=
    continuous_subtype_val.comp continuous_fst
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : (z.2 : ℝ) = 1
  · change Tendsto compactifiedPolar (𝓝 z) (𝓝 (compactifiedPolar z))
    rw [show compactifiedPolar z = ∞ by simp only [compactifiedPolar, hz, if_true]]
    apply OnePoint.hasBasis_nhds_infty.tendsto_right_iff.mpr
    intro K hK
    obtain ⟨R, hR, hKR⟩ := hK.2.isBounded.subset_ball_lt 0 (0 : E)
    have hRp : 0 < R + 1 := by linarith
    have ha : (R - 1) / (R + 1) < (1 : ℝ) :=
      (div_lt_iff₀ hRp).mpr (by linarith)
    have hn : ∀ᶠ w : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 in 𝓝 z,
        (R - 1) / (R + 1) < (w.2 : ℝ) :=
      (isOpen_lt continuous_const ht).mem_nhds (by
        change (R - 1) / (R + 1) < (z.2 : ℝ)
        rw [hz]
        exact ha)
    filter_upwards [hn] with w hw
    by_cases hwtop : (w.2 : ℝ) = 1
    · exact Or.inr (by simp only [compactifiedPolar, hwtop, if_true, mem_singleton_iff])
    · have hwt : (w.2 : ℝ) < 1 := lt_of_le_of_ne w.2.property.2 hwtop
      have hlarge : R < polarRadius w.2 := by
        apply (lt_div_iff₀ (sub_pos.mpr hwt)).mpr
        have hmul := (div_lt_iff₀ hRp).mp hw
        nlinarith
      refine Or.inl ⟨(polarRadius w.2) • (w.1 : E), ?_, ?_⟩
      · intro hm
        have hsmall := mem_ball_zero_iff.mp (hKR hm)
        rw [norm_polarVector w hwt] at hsmall
        exact lt_asymm hlarge hsmall
      · simp only [compactifiedPolar, hwtop, if_false]
  · have hden : (1 : ℝ) - (z.2 : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have hr : ContinuousAt
        (fun w : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 => polarRadius w.2) z :=
      (continuous_const.add ht).continuousAt.div (continuous_const.sub ht).continuousAt hden
    have hf : ContinuousAt
        (fun w : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 =>
          (((polarRadius w.2) • (w.1 : E) : E) : OnePoint E)) z :=
      OnePoint.continuous_coe.continuousAt.comp (hr.smul hu.continuousAt)
    apply hf.congr_of_eventuallyEq
    have hn : ∀ᶠ w : sphere (0 : E) 1 × Icc (-1 : ℝ) 1 in 𝓝 z, (w.2 : ℝ) ≠ 1 :=
      ((isOpen_ne : IsOpen {t : ℝ | t ≠ 1}).preimage ht).mem_nhds hz
    filter_upwards [hn] with w hw
    simp only [compactifiedPolar, hw, if_false]

end BrownSchoenflies
