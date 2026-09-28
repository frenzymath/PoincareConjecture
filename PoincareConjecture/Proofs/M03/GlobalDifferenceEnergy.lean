import PoincareConjecture.Proofs.M03.ScalarEnergyComparison

set_option autoImplicit false

open Set

namespace PoincareConjecture.Proofs.M03

theorem energy_rate_le_of_coupled_component_rates
    {rH rA rS CH CA CS E D : ℝ}
    (hH : rH ≤ CH * E)
    (hA : rA ≤ CA * E + (1 / 2 : ℝ) * D)
    (hS : rS ≤ CS * E - D) :
    rH + rA + rS ≤ (CH + CA + CS) * E - (1 / 2 : ℝ) * D := by
  linarith

theorem energy_eq_zero_on_common_interval_of_interior_slabs
    {E : ℝ → ℝ} {J K : Set ℝ}
    (hJ : J.OrdConnected) (hK : K.OrdConnected)
    (hJ0 : IsLeast J 0) (hK0 : IsLeast K 0) (hE0 : E 0 = 0)
    (hcont : ContinuousOn E (J ∩ K))
    (hnonneg : ∀ t ∈ J ∩ K, 0 ≤ E t)
    (hslab : ∀ b ∈ interior (J ∩ K), 0 < b → ∃ C : ℝ, ∃ rate : ℝ → ℝ,
      (∀ t ∈ Ioo 0 b, HasDerivWithinAt E (rate t) (J ∩ K) t) ∧
      (∀ t ∈ Ioo 0 b, rate t ≤ C * E t)) :
    EqOn E (fun _ => 0) (J ∩ K) := by
  have hcommon {b : ℝ} (hb : b ∈ J ∩ K) : Icc 0 b ⊆ J ∩ K := by
    intro s hs
    exact ⟨hJ.out hJ0.1 hb.1 hs, hK.out hK0.1 hb.2 hs⟩
  have hinterior {b : ℝ} (hb : b ∈ J ∩ K) :
      Ioo 0 b ⊆ interior (J ∩ K) := by
    apply interior_maximal
      (Ioo_subset_Icc_self.trans (hcommon hb))
      isOpen_Ioo
  intro t ht
  have ht0 : 0 ≤ t := hJ0.2 ht.1
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · exact hE0
  have hzero_lt : ∀ s ∈ Ioo 0 t, E s = 0 := by
    intro s hs
    let b := (s + t) / 2
    have hbpos : 0 < b := by
      dsimp [b]
      linarith [hs.1]
    have hsb : s < b := by
      dsimp [b]
      linarith [hs.2]
    have hbt : b < t := by
      dsimp [b]
      linarith [hs.2]
    have hbdom : b ∈ J ∩ K := hcommon ht ⟨hbpos.le, hbt.le⟩
    have hbint : b ∈ interior (J ∩ K) := hinterior ht ⟨hbpos, hbt⟩
    obtain ⟨C, rate, hderiv, hbound⟩ := hslab b hbint hbpos
    have hIcc : Icc 0 b ⊆ J ∩ K := hcommon hbdom
    have hcont' : ContinuousOn E (Icc 0 b) := hcont.mono hIcc
    have hnonneg' : ∀ r ∈ Icc 0 b, 0 ≤ E r := fun r hr =>
      hnonneg r (hIcc hr)
    have hdiff : ∀ r ∈ Ioo 0 b, DifferentiableAt ℝ E r := by
      intro r hr
      have hd := (hderiv r hr).mono hIcc
      exact (hd.hasDerivAt (Icc_mem_nhds hr.1 hr.2)).differentiableAt
    have hrate : ∀ r ∈ Ioo 0 b, deriv E r ≤ C * E r := by
      intro r hr
      have hd := (hderiv r hr).mono hIcc
      rw [(hd.hasDerivAt (Icc_mem_nhds hr.1 hr.2)).deriv]
      exact hbound r hr
    have hzero := eq_zero_on_interval_of_deriv_le_mul hcont' hdiff hE0
      hnonneg' hrate
    exact hzero ⟨hs.1.le, hsb.le⟩
  have hzero_co : EqOn E (fun _ => 0) (Ico 0 t) := by
    intro s hs
    rcases hs.1.eq_or_lt with rfl | hspos
    · exact hE0
    · exact hzero_lt s ⟨hspos, hs.2⟩
  have hzero_cc := hzero_co.of_subset_closure (hcont.mono (hcommon ht))
    continuousOn_const Ico_subset_Icc_self (by rw [closure_Ico htpos.ne])
  simpa only using hzero_cc ⟨htpos.le, le_rfl⟩

end PoincareConjecture.Proofs.M03
