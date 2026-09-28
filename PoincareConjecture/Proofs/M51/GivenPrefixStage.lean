import PoincareConjecture.Proofs.M51.EpochStage
import PoincareConjecture.Proofs.M51.NumericalSchedule
import PoincareConjecture.Proofs.M51.EpochIndex
import PoincareConjecture.Proofs.M51.PrefixVolumeControls
import PoincareConjecture.Proofs.M51.HorizonCount
import PoincareConjecture.Proofs.M51.LastSlab
import PoincareConjecture.Proofs.M51.EmptyControlledExtension

set_option autoImplicit false

open Set
open scoped ENNReal

universe u

namespace PoincareConjecture.M51

open M51Numerical

theorem epochStage_of_controlledPrefix
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S}
    {C : RepairedCanonicalInductionData S N}
    {delta : ℝ → ℝ} {F : SurgeryFlowData.{u}} {H : ℝ}
    (P : RepairedGlobalControlledPrefix (M51Numerical.schedule S N C) delta F H)
    (hdelta : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (M51Numerical.schedule S N C).Delta j)
    (tail : MaximalTail F) (n : ℕ)
    (hlo : surgeryEpochStart (n + 1) ≤ H)
    (hhi : H ≤ surgeryEpochStart (n + 2)) :
    ∃ X : EpochStage S N C n F,
      X.extension = SurgeryFlowExtension.refl F ∧ X.observation.H = H := by
  let O : SurgeryObservation F := P.observation
  have hprefix : SurgeryPrefixControls (prefixAt S N C n) F O := by
    have hsetup : (prefixAt S N C n).setup = S.setup :=
      prefix_setup S N C n
    refine {
      standard_initial_eq := ?_
      local_constants_eq := P.local_constants_eq
      epsilon_eq := ?_
      C_eq := ?_
      admissible := P.admissible
      pinched := ?_
      canonical := ?_
      noncollapsed := ?_
      delta_bound := ?_
      r_schedule := ?_
      kappa_schedule := ?_
      h_schedule := ?_ }
    · rw [hsetup]
      exact P.standard_initial_eq
    · rw [hsetup]
      exact P.parameters_epsilon_eq
    · rw [hsetup]
      exact P.parameters_C_eq
    · intro t ht htF
      exact P.pinched t htF
    · intro j hj t ht
      have ht0 : 0 ≤ t := ht.1.1
      have hentry := ht.2
      have hprofile := P.schedule_agreement j.val t hentry ht0
      have hp := M51Numerical.prefix_agreement S N C n j
      intro htF x hcurv
      apply P.canonical t htF x
      rw [hprofile.1, hp.1]
      exact hcurv
    · intro j hj t ht
      have ht0 : 0 ≤ t := ht.1.1
      have hentry := ht.2
      have hprofile := P.schedule_agreement j.val t hentry ht0
      have hp := M51Numerical.prefix_agreement S N C n j
      intro htF x hpositive r hr hre e hzero hcurv
      have hbound := P.noncollapsed t htF x hpositive r hr hre e hzero hcurv
      rw [hprofile.2.1, hp.2.1] at hbound
      exact hbound
    · intro j hj t ht
      have ht0 : 0 ≤ t := ht.1.1
      have hentry := ht.2
      have hprofile := P.schedule_agreement j.val t hentry ht0
      have hp := M51Numerical.prefix_agreement S N C n j
      rw [P.delta_eq t ht0]
      exact (hdelta j.val t hentry ht0).trans (hp.2.2)
    · intro j hj t ht
      have ht0 : 0 ≤ t := ht.1.1
      have hprofile := P.schedule_agreement j.val t ht.2 ht0
      exact hprofile.1.trans (M51Numerical.prefix_agreement S N C n j).1
    · intro j hj t ht
      have ht0 : 0 ≤ t := ht.1.1
      have hprofile := P.schedule_agreement j.val t ht.2 ht0
      exact hprofile.2.1.trans (M51Numerical.prefix_agreement S N C n j).2.1
    · intro j hj t ht
      have ht0 : 0 ≤ t := ht.1.1
      rw [prefix_setup, P.delta_eq t ht0]
      exact (P.schedule_agreement j.val t ht.2 ht0).2.2
  have hfront : H < surgeryEpochStart ((prefixAt S N C n).i + 1) →
      F.time_domain = Ico 0 O.H := by
    intro _
    simpa [O, RepairedGlobalControlledPrefix.observation] using P.time_domain_eq
  refine ⟨EpochStage.ofObservation O hprefix P.pinched P.terminal_policy tail
      (by simpa only [O, RepairedGlobalControlledPrefix.observation, prefix_index] using hlo)
      (by simpa only [O, RepairedGlobalControlledPrefix.observation, prefix_index] using hhi)
      hfront, rfl, rfl⟩

theorem controlledPrefix_epoch
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S}
    {C : RepairedCanonicalInductionData S N}
    {delta : ℝ → ℝ} {F : SurgeryFlowData.{u}} {H : ℝ}
    (P : RepairedGlobalControlledPrefix (M51Numerical.schedule S N C) delta F H) :
    ∃ n : ℕ, surgeryEpochStart (n + 1) ≤ H ∧ H ≤ surgeryEpochStart (n + 2) := by
  have hstart : surgeryEpochStart 1 < H := by
    have h := S.initialFrontier_lt F H P.horizon_pos P.time_domain_eq
    norm_num [surgeryEpochStart] at ⊢
    exact h
  have hindex : 2 ≤ epochIndex H := by
    by_contra h
    have hi : epochIndex H ≤ 1 := by omega
    exact (lt_irrefl H) ((lt_epochStart_index H).trans
      ((epochStart_strictMono.monotone hi).trans_lt hstart))
  refine ⟨epochIndex H - 2, ?_, ?_⟩
  · exact epochStart_le_of_lt_index (by omega)
  · have hi : epochIndex H - 2 + 2 = epochIndex H := by omega
    rw [hi]
    exact (lt_epochStart_index H).le

theorem controlledPrefix_start
    {S : RepairedControlledSchedulesData.{u}}
    {N : RepairedNoncollapseInductionData S}
    {C : RepairedCanonicalInductionData S N}
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (V50 : RepairedFinitePrefixTheory.{u})
    (d : ℝ) (hd : (M51Numerical.schedule S N C).Delta 0 ≤ d)
    (losses : ∀ (F : SurgeryFlowData.{u}) (V : RepairedVolumeLossControls F),
      F.standard_initial = S.setup.standard_initial → F.local_constants = S.constants →
      (∀ t ∈ F.surgery_times, F.parameters.delta t ≤ d) →
      Nonempty (RepairedVolumeLossData F V))
    {delta : ℝ → ℝ} {F : SurgeryFlowData.{u}} {H : ℝ}
    (P : RepairedGlobalControlledPrefix (M51Numerical.schedule S N C) delta F H)
    (hdelta : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (M51Numerical.schedule S N C).Delta j) :
    Nonempty (RepairedGlobalControlledExtension (M51Numerical.schedule S N C) F) ∨
      ∃ n : ℕ, ∃ X : EpochStage S N C n F,
        X.extension = SurgeryFlowExtension.refl F ∧ X.observation.H = H := by
  obtain ⟨_V, _hV, hfinite⟩ := selectedPrefixLoss
    (M51Numerical.schedule S N C) H13 V50 d hd losses hdelta P
  obtain ⟨a, ha, _hstart, haH, _hI, _hS, halt⟩ :=
    F.lastSlabAlternative H13 P.time_domain_eq hfinite
  rcases halt with hempty | ⟨L, _hL⟩
  · let := hempty a ⟨le_rfl, haH⟩
    exact Or.inl ⟨M51Empty.controlledExtension H13 P ha hdelta⟩
  · have htail : MaximalTail F :=
      Or.inr ⟨H, P.horizon_pos, P.time_domain_eq, ⟨L⟩⟩
    obtain ⟨n, hlo, hhi⟩ := controlledPrefix_epoch P
    obtain ⟨X, hX, hH⟩ := epochStage_of_controlledPrefix P hdelta htail n hlo hhi
    exact Or.inr ⟨n, X, hX, hH⟩

end PoincareConjecture.M51
