import PoincareConjecture.Proofs.M08.WeakMomentum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped intervalIntegral ContDiff

namespace PoincareConjecture.M08

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem continuous_primitive_regular {a b : ℝ} (hab : a < b)
    (u q : ℝ → E) (hq : ContinuousOn q (Icc a b))
    (hprimitive : ∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, q r) :
    (∀ s ∈ Icc a b, HasDerivWithinAt u (q s) (Icc a b) s) ∧
      ContDiffOn ℝ 1 u (Icc a b) := by
  have hqint : IntervalIntegrable q volume a b := hq.intervalIntegrable_of_Icc hab.le
  have hderiv (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivWithinAt u (q s) (Icc a b) s := by
    haveI : Fact (s ∈ Icc a b) := ⟨hs⟩
    have hint : IntervalIntegrable q volume a s := hqint.mono_set (by
      rw [uIcc_of_le hs.1, uIcc_of_le hab.le]
      exact Icc_subset_Icc_right hs.2)
    have hd := (intervalIntegral.integral_hasDerivWithinAt_right
      (s := Icc a b) (t := Icc a b) hint
      (hq.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s) (hq s hs)).const_add
        (u a)
    exact hd.congr_of_mem hprimitive hs
  refine ⟨hderiv, ?_⟩
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)]
  refine ⟨fun s hs ↦ (hderiv s hs).differentiableWithinAt, hq.congr ?_⟩
  intro s hs
  exact (hderiv s hs).derivWithin (uniqueDiffOn_Icc hab s hs)

theorem weak_velocity_regular {a b : ℝ} (hab : a < b)
    (u : ℝ → E) (w : ChartL2 E a b)
    (hprimitive : ∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, w r)
    (A B : ℝ → E →L[ℝ] E)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hinv : ∀ s ∈ Icc a b, ∀ v : E, B s (A s v) = v)
    (Q : ℝ → E) (hQ : IntervalIntegrable Q volume a b)
    (hP : IntervalIntegrable (fun s ↦ A s (w s)) volume a b)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ s in a..b, deriv φ s • A s (w s)) =
        -(∫ s in a..b, φ s • Q s)) :
    ∃ (c : E) (q : ℝ → E),
      (∀ s, q s = B s (c + ∫ r in a..s, Q r)) ∧
      ContinuousOn q (Icc a b) ∧
      (w : ℝ → E) =ᵐ[volume.restrict (Icc a b)] q ∧
      (∀ s ∈ Icc a b, A s (q s) = c + ∫ r in a..s, Q r) ∧
      (∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, q r) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt u (q s) (Icc a b) s) ∧
      ContDiffOn ℝ 1 u (Icc a b) := by
  obtain ⟨c, hc⟩ := weak_momentum_primitive hab (fun s ↦ A s (w s)) Q hP hQ hweak
  let q : ℝ → E := fun s ↦ B s (c + ∫ r in a..s, Q r)
  have hH : ContinuousOn (fun s ↦ c + ∫ r in a..s, Q r) (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hQ left_mem_uIcc
    rw [uIcc_of_le hab.le] at h
    exact continuousOn_const.add h
  have hq : ContinuousOn q (Icc a b) := hB.clm_apply hH
  have hwq : (w : ℝ → E) =ᵐ[volume.restrict (Icc a b)] q := by
    filter_upwards [hc, ae_restrict_mem measurableSet_Icc] with s hs hmem
    dsimp only [q]
    rw [← hs]
    exact (hinv s hmem (w s)).symm
  have hmomentum : ∀ s ∈ Icc a b, A s (q s) = c + ∫ r in a..s, Q r := by
    apply Measure.eqOn_Icc_of_ae_eq volume hab.ne
    · filter_upwards [hc, hwq] with s hs hws
      rw [← hws]
      exact hs
    · exact hA.clm_apply hq
    · exact hH
  have hprimitiveQ (s : ℝ) (hs : s ∈ Icc a b) :
      u s = u a + ∫ r in a..s, q r := by
    rw [hprimitive s hs]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hs.1]
    exact ae_mono (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hs.2)) le_rfl) hwq
  obtain ⟨hderiv, hC1⟩ := continuous_primitive_regular hab u q hq hprimitiveQ
  exact ⟨c, q, fun _ ↦ rfl, hq, hwq, hmomentum, hprimitiveQ, hderiv, hC1⟩

end PoincareConjecture.M08
