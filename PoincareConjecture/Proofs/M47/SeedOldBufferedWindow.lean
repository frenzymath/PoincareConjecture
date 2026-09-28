import PoincareConjecture.Proofs.M47.SeedYoungBirthScales









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47



theorem seed_old_buffered_birth_search_window
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (hEnd : surgeryEpochStart p.i < O.H)
    {T d a : ℝ}
    (hT : T ∈ Icc (surgeryEpochStart p.i - 1 / 128) (surgeryEpochStart p.i))
    (hd : 0 ≤ d) (hyoung : d ≤ (p.r (Fin.last p.i)) ^ 2 / 32)
    (ha : a ≤ (p.r (Fin.last p.i)) ^ 2 / 624) :
    Icc (T - d - a) (T - d) ⊆
      surgeryObservationInterval O ∩ Ici (surgeryEpochStart (p.i - 1)) := by
  have hr := p.r_pos (Fin.last p.i)
  have hsmall : p.r (Fin.last p.i) ≤ 1 / 200 :=
    (p.r_le_epsilon _).trans (p.setup.epsilon_le.trans (min_le_left _ _))
  have hsquare := pow_le_pow_left₀ hr.le hsmall 2
  have hprevious : 1 / 32 ≤ surgeryEpochStart (p.i - 1) :=
    div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (by norm_num)
  have hepoch : surgeryEpochStart p.i = 2 * surgeryEpochStart (p.i - 1) := by
    calc
      surgeryEpochStart p.i = surgeryEpochStart (p.i - 1 + 1) := by
        rw [Nat.sub_add_cancel p.i_pos]
      _ = 2 * surgeryEpochStart (p.i - 1) := by
        unfold surgeryEpochStart
        rw [pow_succ]
        ring
  intro s hs
  have hlower : surgeryEpochStart (p.i - 1) ≤ s := by
    rw [hepoch] at hT
    nlinarith only [hs.1, hT.1, hprevious, hsquare, hyoung, ha]
  have hnonnegative : 0 ≤ surgeryEpochStart (p.i - 1) := by
    linarith only [hprevious]
  exact ⟨⟨hnonnegative.trans hlower,
    by linarith only [hs.2, hd, hT.2, hEnd]⟩, hlower⟩

end PoincareConjecture.Proofs.M47
