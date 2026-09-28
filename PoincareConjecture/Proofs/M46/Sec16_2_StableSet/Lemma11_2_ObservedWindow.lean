import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_EpochWindow










set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M46



theorem ObservedInputs.cutoff_mono {K : MetricSurgeryConstants}
    {p : SurgeryParameterPrefix K} {rNext delta delta' : ℝ}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext delta F O) (hdelta : delta ≤ delta') :
    ObservedInputs p rNext delta' F O := {
  inputs with
  scales := {
    r_eq := inputs.scales.r_eq
    delta_le := fun t ht => (inputs.scales.delta_le t ht).trans hdelta
    h_eq := inputs.scales.h_eq
  }
  overlap := fun t ht => (inputs.overlap t ht).trans hdelta
}



theorem observed_low_cylinder_window {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {rNext cutoff B : ℝ}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (inputs : ObservedInputs p rNext cutoff F O) (D : NoncollapseTest F O)
    (hnew : surgeryEpochStart p.i ≤ D.time) (hB : 1 ≤ B)
    (hr : 0 < rNext) (hrLast : rNext ≤ p.r (Fin.last p.i)) :
    Icc (D.time - rNext ^ 2 / (64 * B)) D.time ⊆
      surgeryObservationInterval O ∩ overlapInterval p := by
  have hrsmall : rNext ≤ 1 / 200 :=
    hrLast.trans ((p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _)))
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hshort : rNext ^ 2 / (64 * B) ≤ 1 / 40000 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hBpos)).mpr
    nlinarith [sq_nonneg (rNext - 1 / 200)]
  have ha := epochStart_ge_initial (p.i - 1)
  rw [prefix_epochStart_eq_twice p] at hnew
  intro t ht
  have htlo : surgeryEpochStart (p.i - 1) ≤ t := by linarith [ht.1]
  have hthi : t < O.H := ht.2.trans_lt D.time_mem.2
  exact ⟨⟨by linarith, hthi⟩, htlo, hthi.trans_le inputs.next_epoch.2⟩



theorem NoncollapseTest.exists_later_observed_time
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} (D : NoncollapseTest F O) :
    ∃ top : ℝ, D.time < top ∧ top ∈ F.time_domain := by
  obtain ⟨top, htop, htopH⟩ := exists_between D.time_mem.2
  exact ⟨top, htop, O.interval_subset ⟨D.time_mem.1.trans htop.le, htopH⟩⟩

end PoincareConjecture.Proofs.M46
