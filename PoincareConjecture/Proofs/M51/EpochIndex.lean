import PoincareConjecture.Proofs.M51.EpochCoverage

set_option autoImplicit false

namespace PoincareConjecture
namespace M51Numerical

theorem epochStart_strictMono : StrictMono surgeryEpochStart := by
  intro i j hij
  exact div_lt_div_of_pos_right
    (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hij) (by norm_num)

theorem exists_lt_epochStart (t : ℝ) : ∃ j : ℕ, t < surgeryEpochStart j := by
  obtain ⟨j, _, hj⟩ := exists_nat_pow_near (le_max_left (1 : ℝ) (32 * t))
    (by norm_num : (1 : ℝ) < 2)
  have hbound := (le_max_right (1 : ℝ) (32 * t)).trans_lt hj
  refine ⟨j + 1, ?_⟩
  dsimp [surgeryEpochStart]
  linarith

noncomputable def epochIndex (t : ℝ) : ℕ := by
  classical
  exact Nat.find (exists_lt_epochStart t)

theorem lt_epochStart_index (t : ℝ) : t < surgeryEpochStart (epochIndex t) := by
  classical
  exact Nat.find_spec (exists_lt_epochStart t)

theorem epochIndex_le {t : ℝ} {j : ℕ} (ht : t < surgeryEpochStart j) :
    epochIndex t ≤ j := by
  classical
  exact Nat.find_min' (exists_lt_epochStart t) ht

theorem epochStart_le_of_lt_index {t : ℝ} {j : ℕ} (hj : j < epochIndex t) :
    surgeryEpochStart j ≤ t := by
  classical
  exact not_lt.mp (Nat.find_min (exists_lt_epochStart t) hj)

theorem epochIndex_monotone : Monotone epochIndex := by
  intro s t hst
  exact epochIndex_le (hst.trans_lt (lt_epochStart_index t))

theorem epochIndex_eq_zero {t : ℝ} (ht : t < surgeryEpochStart 0) :
    epochIndex t = 0 := Nat.eq_zero_of_le_zero (epochIndex_le ht)

@[simp] theorem epochIndex_zero : epochIndex 0 = 0 :=
  epochIndex_eq_zero (by norm_num [surgeryEpochStart])

theorem epochIndex_of_neg {t : ℝ} (ht : t < 0) : epochIndex t = 0 :=
  epochIndex_eq_zero (ht.trans (by norm_num [surgeryEpochStart]))

@[simp] theorem epochIndex_start (j : ℕ) :
    epochIndex (surgeryEpochStart j) = j + 1 := by
  apply le_antisymm
  · exact epochIndex_le (epochStart_strictMono (Nat.lt_succ_self j))
  · by_contra h
    have hij : epochIndex (surgeryEpochStart j) ≤ j := by omega
    exact (not_lt_of_ge (epochStart_strictMono.monotone hij))
      (lt_epochStart_index (surgeryEpochStart j))

theorem mem_epochEntry_index {t : ℝ} (ht : 0 ≤ t) :
    t ∈ surgeryEpochEntry (epochIndex t) := by
  by_cases hi : epochIndex t = 0
  · simpa [surgeryEpochEntry, hi] using And.intro ht (lt_epochStart_index t)
  · simp only [surgeryEpochEntry, hi, if_false, Set.mem_Ico]
    exact ⟨epochStart_le_of_lt_index (by omega), lt_epochStart_index t⟩

theorem epochIndex_of_mem {t : ℝ} {j : ℕ} (ht : t ∈ surgeryEpochEntry j) :
    epochIndex t = j := by
  by_cases hj : j = 0
  · subst j
    exact epochIndex_eq_zero (by simpa [surgeryEpochEntry] using ht.2)
  · have hbounds : surgeryEpochStart (j - 1) ≤ t ∧ t < surgeryEpochStart j := by
      simpa [surgeryEpochEntry, hj] using ht
    apply le_antisymm (epochIndex_le hbounds.2)
    by_contra h
    have hij : epochIndex t ≤ j - 1 := by omega
    exact (not_lt_of_ge (hbounds.1.trans' (epochStart_strictMono.monotone hij)))
      (lt_epochStart_index t)

theorem epochEntry_unique {t : ℝ} {i j : ℕ}
    (hi : t ∈ surgeryEpochEntry i) (hj : t ∈ surgeryEpochEntry j) : i = j :=
  (epochIndex_of_mem hi).symm.trans (epochIndex_of_mem hj)

end M51Numerical
end PoincareConjecture
