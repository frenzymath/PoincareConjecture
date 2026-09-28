import PoincareConjecture.Proofs.M08.WeakVelocity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff intervalIntegral

namespace PoincareConjecture.M08

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_continuous_endpoint_momentum {a b : ℝ} (hab : a < b)
    (P Q : ℝ → E) (hQ : IntervalIntegrable Q volume a b)
    (hP : ∀ s ∈ Ioo a b, HasDerivAt P (Q s) s) :
    ∃ c : E, ∀ s ∈ Ioo a b, P s = c + ∫ r in a..s, Q r := by
  let d := (a + b) / 2
  have hd : d ∈ Ioo a b := ⟨by dsimp only [d]; linarith, by dsimp only [d]; linarith⟩
  have hQsub {r s : ℝ} (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) :
      IntervalIntegrable Q volume r s := hQ.mono_set (by
    rw [uIcc_of_le hab.le]
    exact uIcc_subset_Icc hr hs)
  refine ⟨P d - ∫ r in a..d, Q r, ?_⟩
  intro s hs
  have hsub : uIcc d s ⊆ Ioo a b := by
    intro r hr
    exact ⟨lt_of_lt_of_le (lt_min hd.1 hs.1) hr.1,
      lt_of_le_of_lt hr.2 (max_lt hd.2 hs.2)⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr ↦ hP r (hsub hr)) (hQsub (Ioo_subset_Icc_self hd) (Ioo_subset_Icc_self hs))
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hQsub ⟨le_rfl, hab.le⟩ (Ioo_subset_Icc_self hd))
    (hQsub (Ioo_subset_Icc_self hd) (Ioo_subset_Icc_self hs))
  rw [hFTC] at hadd
  rw [← hadd]
  abel


theorem endpoint_velocity_of_momentum {a b : ℝ} (hab : a < b)
    (u d P Q : ℝ → E)
    (hu : ContinuousOn u (Icc a b))
    (hud : ∀ s ∈ Ioo a b, HasDerivAt u (d s) s)
    (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (A B : ℝ → E →L[ℝ] E)
    (hB : ContinuousOn B (Icc a b))
    (hinv : ∀ s ∈ Icc a b, ∀ v : E, B s (A s v) = v)
    (hPdef : ∀ s ∈ Ioo a b, P s = A s (d s))
    (hQ : IntervalIntegrable Q volume a b)
    (hPd : ∀ s ∈ Ioo a b, HasDerivAt P (Q s) s) :
    ∃ (c : E) (q Pbar : ℝ → E),
      (∀ s, Pbar s = c + ∫ r in a..s, Q r) ∧
      (∀ s, q s = B s (Pbar s)) ∧
      ContinuousOn Pbar (Icc a b) ∧ ContinuousOn q (Icc a b) ∧
      EqOn Pbar P (Ioo a b) ∧ EqOn q d (Ioo a b) ∧
      (∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, q r) ∧
      (∀ s ∈ Icc a b, HasDerivWithinAt u (q s) (Icc a b) s) ∧
      ContDiffOn ℝ 1 u (Icc a b) := by
  obtain ⟨c, hc⟩ := exists_continuous_endpoint_momentum hab P Q hQ hPd
  let Pbar : ℝ → E := fun s ↦ c + ∫ r in a..s, Q r
  let q : ℝ → E := fun s ↦ B s (Pbar s)
  have hPc : ContinuousOn Pbar (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hQ left_mem_uIcc
    rw [uIcc_of_le hab.le] at h
    exact continuousOn_const.add h
  have hqc : ContinuousOn q (Icc a b) := hB.clm_apply hPc
  have hqeq : EqOn q d (Ioo a b) := by
    intro s hs
    dsimp only [q, Pbar]
    rw [← hc s hs, hPdef s hs, hinv s (Ioo_subset_Icc_self hs)]
  have hdq : d =ᵐ[volume.restrict (Icc a b)] q := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hqeq hs).symm
  have hprimitive (s : ℝ) (hs : s ∈ Icc a b) :
      u s = u a + ∫ r in a..s, q r := by
    rw [chart_primitive_of_deriv hu hud hd hs]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hs.1]
    exact ae_mono (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hs.2)) le_rfl)
      (hd.coeFn_toLp.trans hdq)
  obtain ⟨hderiv, hsmooth⟩ := continuous_primitive_regular hab u q hqc hprimitive
  exact ⟨c, q, Pbar, fun _ ↦ rfl, fun _ ↦ rfl, hPc, hqc,
    fun s hs ↦ (hc s hs).symm, hqeq, hprimitive, hderiv, hsmooth⟩

theorem endpoint_momentum_derivative_of_continuous_force {a b : ℝ} (hab : a < b)
    (c : E) (Q Qbar : ℝ → E)
    (heq : EqOn Qbar Q (Ioo a b)) (hQbar : ContinuousOn Qbar (Icc a b)) :
    ∀ s ∈ Icc a b, HasDerivWithinAt
      (fun t ↦ c + ∫ r in a..t, Q r) (Qbar s) (Icc a b) s := by
  let Pbar : ℝ → E := fun t ↦ c + ∫ r in a..t, Q r
  have heqint (s : ℝ) (hs : s ∈ Icc a b) :
      (∫ r in a..s, Q r) = ∫ r in a..s, Qbar r := by
    apply intervalIntegral.integral_congr_Ioo_of_le hs.1
    intro r hr
    exact (heq ⟨hr.1, hr.2.trans_le hs.2⟩).symm
  have hprimitive (s : ℝ) (hs : s ∈ Icc a b) :
      Pbar s = Pbar a + ∫ r in a..s, Qbar r := by
    simp only [Pbar, intervalIntegral.integral_same, add_zero, heqint s hs]
  exact (continuous_primitive_regular hab Pbar Qbar hQbar hprimitive).1

end PoincareConjecture.M08
