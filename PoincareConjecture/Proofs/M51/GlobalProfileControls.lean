import PoincareConjecture.Proofs.M51.CompletedStageChain
import PoincareConjecture.Proofs.M48.ExtensionNoncollapse










set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M51.CompletedStageChain

open M51Numerical

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F₀ : SurgeryFlowData.{u}} {k : ℕ}
  (Q : CompletedStageChain S N C F₀ k)


theorem exists_observed_entry (t : ℝ) (ht : 0 ≤ t) :
    ∃ n, ∃ j : Fin ((prefixAt S N C (k + n)).i + 1),
      t ∈ surgeryObservationInterval (Q.observation n) ∩ surgeryEpochEntry j.val := by
  obtain ⟨n, hn, hH⟩ := Q.exists_later_horizon (epochIndex t) t
  have hj : epochIndex t < (prefixAt S N C (k + n)).i + 1 := by
    rw [prefix_index]
    omega
  exact ⟨n, ⟨epochIndex t, hj⟩, ⟨ht, hH⟩, mem_epochEntry_index ht⟩


theorem canonical_of_extensions
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (G : SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (Q.flow n))
    (hE : ∀ n, (E n).extended = G) : SurgeryCanonicalAssumption G := by
  intro t ht x hx
  obtain ⟨n, j, hentry⟩ := Q.exists_observed_entry t (G.time_domain_nonnegative ht)
  have hj : j.val ≤ (prefixAt S N C (k + n)).i := Nat.le_of_lt_succ j.isLt
  have hJ : surgeryObservationInterval (Q.observation n) ∩ surgeryEpochEntry j.val ⊆
      (Q.flow n).time_domain := fun _ hs => (Q.observation n).interval_subset hs.1
  have hcanonical := (E n).canonical_on H13 hJ ((Q.old_controls n).canonical j hj)
  rw [hE n] at hcanonical
  have hr : G.parameters.r t = (prefixAt S N C (k + n)).r j := by
    rw [← hE n, (E n).parameters_eq]
    exact (Q.old_controls n).r_schedule j hj t hentry
  rw [hr] at hx
  exact hcanonical t hentry ht x hx


theorem noncollapsed_of_extensions
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (G : SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (Q.flow n))
    (hE : ∀ n, (E n).extended = G) : SurgeryNoncollapsed G := by
  intro t ht x hpositive r hr hrepsilon cylinder hterminal hcurvature
  obtain ⟨n, j, hentry⟩ := Q.exists_observed_entry t (G.time_domain_nonnegative ht)
  have hj : j.val ≤ (prefixAt S N C (k + n)).i := Nat.le_of_lt_succ j.isLt
  have hJ : surgeryObservationInterval (Q.observation n) ∩ surgeryEpochEntry j.val ⊆
      (Q.flow n).time_domain := fun _ hs => (Q.observation n).interval_subset hs.1
  have hnoncollapsed :=
    (E n).noncollapsed_on H13 hJ ((Q.old_controls n).noncollapsed j hj)
  rw [hE n] at hnoncollapsed
  have hkappa : G.parameters.kappa t = (prefixAt S N C (k + n)).kappa j := by
    rw [← hE n, (E n).parameters_eq]
    exact (Q.old_controls n).kappa_schedule j hj t hentry
  rw [hkappa]
  exact hnoncollapsed t hentry ht x hpositive r hr hrepsilon cylinder hterminal hcurvature


theorem profile_controls_of_extensions
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (G : SurgeryFlowData.{u})
    (E : ∀ n, SurgeryFlowExtension (Q.flow n))
    (hE : ∀ n, (E n).extended = G) :
    SurgeryCanonicalAssumption G ∧ SurgeryNoncollapsed G :=
  ⟨Q.canonical_of_extensions H13 G E hE, Q.noncollapsed_of_extensions H13 G E hE⟩

end PoincareConjecture.M51.CompletedStageChain
