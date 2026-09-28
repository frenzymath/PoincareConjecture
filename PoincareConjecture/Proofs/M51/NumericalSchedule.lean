import PoincareConjecture.Proofs.M51.NumericalPrefixes
import PoincareConjecture.Proofs.M45.PrefixWitness

set_option autoImplicit false

universe u

namespace PoincareConjecture
namespace M51Numerical

variable (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (C : RepairedCanonicalInductionData S N)

noncomputable def r (j : ℕ) : ℝ := rAt S N C j j (Nat.le_succ j)

noncomputable def kappa (j : ℕ) : ℝ := kappaAt S N C j j (Nat.le_succ j)

noncomputable def delta (j : ℕ) : ℝ := deltaAt S N C j j (Nat.le_succ j)

theorem r_agrees (n j : ℕ) (hj : j ≤ n + 1) :
    r S N C j = rAt S N C n j hj := by
  by_cases hjn : j ≤ n
  · exact (rAt_stable S N C j j n (Nat.le_succ j) hjn).symm
  · have heq : j = n + 1 := by omega
    subst j
    exact rAt_succ S N C n (n + 1) le_rfl

theorem kappa_agrees (n j : ℕ) (hj : j ≤ n + 1) :
    kappa S N C j = kappaAt S N C n j hj := by
  by_cases hjn : j ≤ n
  · exact (kappaAt_stable S N C j j n (Nat.le_succ j) hjn).symm
  · have heq : j = n + 1 := by omega
    subst j
    exact kappaAt_succ S N C n (n + 1) le_rfl

theorem delta_agrees (n j : ℕ) (hj : j ≤ n) :
    delta S N C j = deltaAt S N C n j (by omega) :=
  (deltaAt_stable S N C j j n le_rfl hj).symm

theorem delta_le_prefix (n j : ℕ) (hj : j ≤ n + 1) :
    delta S N C j ≤ deltaAt S N C n j hj := by
  by_cases hjn : j ≤ n
  · exact (delta_agrees S N C n j hjn).le
  · have heq : j = n + 1 := by omega
    subst j
    exact deltaAt_succ_le S N C n (n + 1) le_rfl

theorem r_pos (j : ℕ) : 0 < r S N C j := (prefixAt S N C j).r_pos _

theorem kappa_pos (j : ℕ) : 0 < kappa S N C j := (prefixAt S N C j).kappa_pos _

theorem delta_pos (j : ℕ) : 0 < delta S N C j := (prefixAt S N C j).Delta_pos _

theorem r_antitone : Antitone (r S N C) := by
  intro j k hjk
  rw [r_agrees S N C k j (by omega), r_agrees S N C k k (by omega)]
  exact (prefixAt S N C k).r_antitone hjk

theorem kappa_antitone : Antitone (kappa S N C) := by
  intro j k hjk
  rw [kappa_agrees S N C k j (by omega), kappa_agrees S N C k k (by omega)]
  exact (prefixAt S N C k).kappa_antitone hjk

theorem delta_antitone : Antitone (delta S N C) := by
  intro j k hjk
  rw [delta_agrees S N C k j hjk, delta_agrees S N C k k le_rfl]
  exact (prefixAt S N C k).Delta_antitone hjk

@[simp] theorem r_zero : r S N C 0 = S.setup.epsilon := rfl

@[simp] theorem kappa_zero : kappa S N C 0 = S.kappa0 := rfl

@[simp] theorem delta_zero : delta S N C 0 = S.Delta0 := rfl

theorem delta_le_seed (j : ℕ) : delta S N C j ≤ S.Delta0 :=
  (delta_antitone S N C (Nat.zero_le j)).trans_eq (delta_zero S N C)

theorem r_next (n : ℕ) : r S N C (n + 2) = (canonical S N C n).rNext := by
  rw [r_agrees S N C (n + 1) (n + 2) le_rfl]
  change ((prefixAt S N C n).nextPrefix (noncollapse S N C n)
    (canonical S N C n)).r _ = _
  convert SurgeryParameterPrefix.nextPrefix_r_last (prefixAt S N C n)
    (noncollapse S N C n) (canonical S N C n) using 1
  congr 1
  apply Fin.ext
  simp only [Fin.val_last, prefix_index]

theorem kappa_next (n : ℕ) :
    kappa S N C (n + 2) = (noncollapse S N C n).kappaNew := by
  rw [kappa_agrees S N C (n + 1) (n + 2) le_rfl]
  change ((prefixAt S N C n).nextPrefix (noncollapse S N C n)
    (canonical S N C n)).kappa _ = _
  convert SurgeryParameterPrefix.nextPrefix_kappa_last (prefixAt S N C n)
    (noncollapse S N C n) (canonical S N C n) using 1
  congr 1
  apply Fin.ext
  simp only [Fin.val_last, prefix_index]

theorem delta_next (n : ℕ) :
    delta S N C (n + 1) = (canonical S N C n).deltaNext := by
  change ((prefixAt S N C n).nextPrefix (noncollapse S N C n)
    (canonical S N C n)).Delta _ = _
  convert SurgeryParameterPrefix.nextPrefix_Delta_penultimate (prefixAt S N C n)
    (noncollapse S N C n) (canonical S N C n) using 1
  congr 1
  apply Fin.ext
  simp only [Fin.val_castSucc, Fin.val_last, prefix_index]

theorem delta_overlap_next (n : ℕ) :
    delta S N C (n + 2) ≤ (canonical S N C n).deltaNext := by
  exact (delta_antitone S N C (Nat.le_succ (n + 1))).trans_eq (delta_next S N C n)

theorem height_antitone (j : ℕ) :
    S.setup.selector.h (delta S N C (j + 1) * r S N C (j + 1))
        (delta S N C (j + 1)) ≤
      S.setup.selector.h (delta S N C j * r S N C j) (delta S N C j) := by
  have hd := delta_antitone S N C (Nat.le_succ j)
  have hr := r_antitone S N C (Nat.le_succ j)
  have hprod := mul_le_mul hd hr (r_pos S N C (j + 1)).le (delta_pos S N C j).le
  exact (S.setup.selector.h_mono_delta _
    (mul_nonneg (delta_pos S N C (j + 1)).le (r_pos S N C (j + 1)).le)
    (delta_pos S N C (j + 1)).le (delta_pos S N C j).le hd).trans
    (S.setup.selector.h_mono_rho _ (delta_pos S N C j).le
      (mul_nonneg (delta_pos S N C (j + 1)).le (r_pos S N C (j + 1)).le)
      (mul_nonneg (delta_pos S N C j).le (r_pos S N C j).le) hprod)

noncomputable def schedule : GlobalSurgerySchedule S.constants where
  setup := S.setup
  epoch := surgeryEpochEntry
  epoch_eq := fun _ => rfl
  r := r S N C
  kappa := kappa S N C
  Delta := delta S N C
  r_pos := r_pos S N C
  kappa_pos := kappa_pos S N C
  Delta_pos := delta_pos S N C
  r_antitone := r_antitone S N C
  kappa_antitone := kappa_antitone S N C
  Delta_antitone := delta_antitone S N C
  r_zero := r_zero S N C
  r_le_epsilon := fun j =>
    (r_antitone S N C (Nat.zero_le j)).trans_eq (r_zero S N C)
  kappa_zero_seed := ⟨S.kappa0, S.calibration.kappa₀_pos, kappa_zero S N C⟩
  Delta_zero_seed := ⟨S.calibration.beta, S.calibration.delta₁₃,
    S.cap_persistence.standard_cap.initial_estimate.core_volume_constant,
    S.cap_persistence.standard_cap.initial_estimate.scalar_constant,
    S.calibration.beta_pos, S.calibration.beta_lt_half, S.calibration.delta₁₃_pos,
    S.cap_persistence.standard_cap.initial_estimate.core_volume_constant_pos,
    S.cap_persistence.standard_cap.initial_estimate.scalar_constant_pos,
    (delta_zero S N C).trans S.calibration.delta_zero_eq⟩
  Delta_le := fun j => (delta_le_seed S N C j).trans S.Delta0_le_setup
  kappa_le := fun j => kappa_antitone S N C (Nat.le_succ j)
  overlap_bound := height_antitone S N C

theorem prefix_agreement (n : ℕ) (j : Fin ((prefixAt S N C n).i + 1)) :
    (schedule S N C).r j.val = (prefixAt S N C n).r j ∧
    (schedule S N C).kappa j.val = (prefixAt S N C n).kappa j ∧
    (schedule S N C).Delta j.val ≤ (prefixAt S N C n).Delta j := by
  have hj : j.val ≤ n + 1 := by
    have := j.isLt
    have := prefix_index S N C n
    omega
  exact ⟨r_agrees S N C n j.val hj, kappa_agrees S N C n j.val hj,
    delta_le_prefix S N C n j.val hj⟩

theorem restriction_agrees (i : ℕ) (hi : 0 < i) (j : Fin (i + 1)) :
    let p := (schedule S N C).parameterPrefix i hi
    let k : Fin ((prefixAt S N C i).i + 1) :=
      ⟨j.val, by rw [prefix_index]; omega⟩
    p.r j = (prefixAt S N C i).r k ∧
    p.kappa j = (prefixAt S N C i).kappa k ∧
    p.Delta j = (prefixAt S N C i).Delta k := by
  exact ⟨r_agrees S N C i j.val (by omega),
    kappa_agrees S N C i j.val (by omega), delta_agrees S N C i j.val (by omega)⟩

theorem cutoff_le (d : ℝ) (hd : S.Delta0 ≤ d) (j : ℕ) :
    (schedule S N C).Delta j ≤ d := (delta_le_seed S N C j).trans hd

theorem overlap_eq (n : ℕ) :
    overlapInterval (prefixAt S N C n) =
      surgeryEpochEntry (n + 1) ∪ surgeryEpochEntry (n + 2) := by
  have hmono : Monotone surgeryEpochStart := by
    intro i j hij
    exact div_le_div_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij) (by norm_num)
  simp only [overlapInterval, prefix_index, surgeryEpochEntry,
    Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
  exact (Set.Ico_union_Ico_eq_Ico (hmono (Nat.le_succ n))
    (hmono (Nat.le_succ (n + 1)))).symm

theorem control_overlap (control : ℝ → ℝ)
    (hcontrol : ∀ j : ℕ, ∀ t ∈ surgeryEpochEntry j,
      control t ≤ (schedule S N C).Delta j)
    (n : ℕ) (t : ℝ) (ht : t ∈ overlapInterval (prefixAt S N C n)) :
    control t ≤ (canonical S N C n).deltaNext := by
  rw [overlap_eq] at ht
  rcases ht with hleft | hright
  · exact (hcontrol (n + 1) t hleft).trans_eq (delta_next S N C n)
  · exact (hcontrol (n + 2) t hright).trans (delta_overlap_next S N C n)

end M51Numerical
end PoincareConjecture
