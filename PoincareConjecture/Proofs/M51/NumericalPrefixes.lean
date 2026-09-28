import PoincareConjecture.Definitions.M45InitialPrefix
import PoincareConjecture.Proofs.M48.PrefixControls

set_option autoImplicit false

universe u

namespace PoincareConjecture
namespace M51Numerical

variable (S : RepairedControlledSchedulesData.{u})
    (N : RepairedNoncollapseInductionData S)
    (C : RepairedCanonicalInductionData S N)

noncomputable def stages : ℕ → {p : SurgeryParameterPrefix S.constants // S.SeedCompatible p}
  | 0 => ⟨S.initialPrefix, S.initialPrefix_seedCompatible⟩
  | n + 1 =>
    let previous := stages n
    let Q := Classical.choice (N.induction previous.val previous.property)
    let R := Classical.choice (C.induction previous.val previous.property)
    ⟨previous.val.nextPrefix Q R, previous.property.nextPrefix Q R⟩

noncomputable def prefixAt (n : ℕ) : SurgeryParameterPrefix S.constants :=
  (stages S N C n).val

theorem compatible (n : ℕ) : S.SeedCompatible (prefixAt S N C n) :=
  (stages S N C n).property

noncomputable def noncollapse (n : ℕ) : SurgeryNoncollapseExtension (prefixAt S N C n) :=
  Classical.choice (N.induction _ (compatible S N C n))

noncomputable def canonical (n : ℕ) :
    SurgeryCanonicalExtension (prefixAt S N C n) (noncollapse S N C n) :=
  Classical.choice (C.induction _ (compatible S N C n))

@[simp] theorem prefix_zero : prefixAt S N C 0 = S.initialPrefix := rfl

theorem prefix_succ (n : ℕ) :
    prefixAt S N C (n + 1) =
      (prefixAt S N C n).nextPrefix (noncollapse S N C n) (canonical S N C n) := rfl

theorem prefix_index (n : ℕ) : (prefixAt S N C n).i = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefix_succ, SurgeryParameterPrefix.nextPrefix_i, ih]

theorem prefix_setup (n : ℕ) : (prefixAt S N C n).setup = S.setup :=
  (compatible S N C n).setup_eq

noncomputable def rAt (n j : ℕ) (hj : j ≤ n + 1) : ℝ :=
  (prefixAt S N C n).r ⟨j, by rw [prefix_index]; omega⟩

noncomputable def kappaAt (n j : ℕ) (hj : j ≤ n + 1) : ℝ :=
  (prefixAt S N C n).kappa ⟨j, by rw [prefix_index]; omega⟩

noncomputable def deltaAt (n j : ℕ) (hj : j ≤ n + 1) : ℝ :=
  (prefixAt S N C n).Delta ⟨j, by rw [prefix_index]; omega⟩

theorem rAt_succ (n j : ℕ) (hj : j ≤ n + 1) :
    rAt S N C (n + 1) j (by omega) = rAt S N C n j hj := by
  exact SurgeryParameterPrefix.nextPrefix_r_castSucc (prefixAt S N C n)
    (noncollapse S N C n) (canonical S N C n) ⟨j, by rw [prefix_index]; omega⟩

theorem kappaAt_succ (n j : ℕ) (hj : j ≤ n + 1) :
    kappaAt S N C (n + 1) j (by omega) = kappaAt S N C n j hj := by
  exact SurgeryParameterPrefix.nextPrefix_kappa_castSucc (prefixAt S N C n)
    (noncollapse S N C n) (canonical S N C n) ⟨j, by rw [prefix_index]; omega⟩

theorem deltaAt_succ (n j : ℕ) (hj : j ≤ n) :
    deltaAt S N C (n + 1) j (by omega) = deltaAt S N C n j (by omega) := by
  exact SurgeryParameterPrefix.nextPrefix_Delta_castSucc_of_lt (prefixAt S N C n)
    (noncollapse S N C n) (canonical S N C n) ⟨j, by rw [prefix_index]; omega⟩
    (by simpa only [prefix_index] using Nat.lt_succ_of_le hj)

theorem deltaAt_succ_le (n j : ℕ) (hj : j ≤ n + 1) :
    deltaAt S N C (n + 1) j (by omega) ≤ deltaAt S N C n j hj := by
  exact SurgeryParameterPrefix.nextPrefix_Delta_castSucc_le (prefixAt S N C n)
    (noncollapse S N C n) (canonical S N C n) ⟨j, by rw [prefix_index]; omega⟩

theorem rAt_stable (j n m : ℕ) (hj : j ≤ n + 1) (hnm : n ≤ m) :
    rAt S N C m j (by omega) = rAt S N C n j hj := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => exact (rAt_succ S N C m j (by omega)).trans ih

theorem kappaAt_stable (j n m : ℕ) (hj : j ≤ n + 1) (hnm : n ≤ m) :
    kappaAt S N C m j (by omega) = kappaAt S N C n j hj := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => exact (kappaAt_succ S N C m j (by omega)).trans ih

theorem deltaAt_stable (j n m : ℕ) (hj : j ≤ n) (hnm : n ≤ m) :
    deltaAt S N C m j (by omega) = deltaAt S N C n j (by omega) := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih => exact (deltaAt_succ S N C m j (by omega)).trans ih

end M51Numerical
end PoincareConjecture
