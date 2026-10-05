import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Seed.EpochWindow

/-!
# The low-cylinder window inside the actual induction overlap

Morgan--Tian Proposition 16.1 and Claim 16.27, pp. 367-368 and 392-393.
The dyadic epoch margin contains the entire short backward cylinder,
including when it crosses into the old epoch. All delta bounds there
come from the literal overlap hypothesis.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.Proofs.M46

/-- An observed flow satisfying a smaller cutoff also satisfies any
larger one, with the same actual radius profile and old prefix. -/
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

/-- The next-epoch low test's full scalar-control window lies in the
observed overlap, including its closed earlier endpoint. -/
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

/-- The tested time has a genuine later observed time, used only to
initialize the actual zero-time identity cylinder. -/
theorem NoncollapseTest.exists_later_observed_time
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F} (D : NoncollapseTest F O) :
    ∃ top : ℝ, D.time < top ∧ top ∈ F.time_domain := by
  obtain ⟨top, htop, htopH⟩ := exists_between D.time_mem.2
  exact ⟨top, htop, O.interval_subset ⟨D.time_mem.1.trans htop.le, htopH⟩⟩

end PoincareMT.Proofs.M46
