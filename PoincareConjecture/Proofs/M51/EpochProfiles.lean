import PoincareConjecture.Proofs.M51.Parameters

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M51Numerical

theorem epochEntry_nonnegative {j : ℕ} {t : ℝ}
    (ht : t ∈ surgeryEpochEntry j) : 0 ≤ t := by
  by_cases hj : j = 0
  · subst j
    exact ht.1
  · have hlo : surgeryEpochStart (j - 1) ≤ t :=
      (show t ∈ Ico (surgeryEpochStart (j - 1)) (surgeryEpochStart j) from
        by simpa [surgeryEpochEntry, hj] using ht).1
    exact (div_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (by norm_num)).trans hlo

variable (S : RepairedControlledSchedulesData.{u})
  (N : RepairedNoncollapseInductionData S) (C : RepairedCanonicalInductionData S N)

theorem stepProfiles (n : ℕ) (F : SurgeryFlowData.{u}) (delta : ℝ → ℝ)
    (hdelta : ∀ t, 0 ≤ t → F.parameters.delta t = delta t)
    (hprofiles : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      F.parameters.r t = (schedule S N C).r j ∧
      F.parameters.kappa t = (schedule S N C).kappa j ∧
      F.parameters.h t = S.setup.selector.h (delta t * F.parameters.r t) (delta t))
    (hcut : ∀ j t, t ∈ surgeryEpochEntry j → 0 ≤ t →
      delta t ≤ (schedule S N C).Delta j) :
    (∀ t ∈ surgeryEpoch (prefixAt S N C n).i,
      F.parameters.r t = (canonical S N C n).rNext) ∧
    (∀ t ∈ surgeryEpoch (prefixAt S N C n).i,
      F.parameters.kappa t = (noncollapse S N C n).kappaNew) ∧
    (∀ t ∈ surgeryEpoch (prefixAt S N C n).i,
      F.parameters.h t = (prefixAt S N C n).setup.selector.h
        (F.parameters.delta t * F.parameters.r t) (F.parameters.delta t)) ∧
    (∀ t ∈ overlapInterval (prefixAt S N C n),
      F.parameters.delta t ≤ (canonical S N C n).deltaNext) := by
  have hentry {t : ℝ} (ht : t ∈ surgeryEpoch (prefixAt S N C n).i) :
      t ∈ surgeryEpochEntry (n + 2) := by
    simpa [surgeryEpochEntry, surgeryEpoch, prefix_index] using ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (hprofiles (n + 2) t (hentry ht) (epochEntry_nonnegative (hentry ht))).1.trans
      (r_next S N C n)
  · intro t ht
    exact (hprofiles (n + 2) t (hentry ht) (epochEntry_nonnegative (hentry ht))).2.1.trans
      (kappa_next S N C n)
  · intro t ht
    rw [prefix_setup, hdelta t (epochEntry_nonnegative (hentry ht))]
    exact (hprofiles (n + 2) t (hentry ht) (epochEntry_nonnegative (hentry ht))).2.2
  · intro t ht
    have ht0 : 0 ≤ t :=
      (div_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) (by norm_num)).trans ht.1
    rw [hdelta t ht0]
    exact control_overlap S N C delta
      (fun j t hj => hcut j t hj (epochEntry_nonnegative hj)) n t ht

end PoincareConjecture.M51Numerical
