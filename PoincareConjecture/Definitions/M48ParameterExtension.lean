import PoincareConjecture.Definitions.Ch16.CanonicalInduction
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

universe u

namespace PoincareConjecture

private theorem antitone_snoc_of_le_last {n : ℕ} {f : Fin (n + 1) → ℝ}
    {a : ℝ} (hf : Antitone f) (ha : a ≤ f (Fin.last n)) :
    Antitone (Fin.snoc f a) := by
  intro j k hjk
  cases j using Fin.lastCases with
  | last =>
      have hk : k = Fin.last (n + 1) := le_antisymm (Fin.le_last k) hjk
      subst k
      exact le_rfl
  | cast j =>
      cases k using Fin.lastCases with
      | last =>
          simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
            ha.trans (hf (Fin.le_last j))
      | cast k =>
          simpa only [Fin.snoc_castSucc] using hf hjk

private theorem antitone_update_last_of_le {n : ℕ} {f : Fin (n + 1) → ℝ}
    {a : ℝ} (hf : Antitone f) (ha : a ≤ f (Fin.last n)) :
    Antitone (Function.update f (Fin.last n) a) := by
  intro j k hjk
  by_cases hk : k = Fin.last n
  · subst k
    by_cases hj : j = Fin.last n
    · subst j
      exact le_rfl
    · simpa [Function.update, hj] using ha.trans (hf (Fin.le_last j))
  · have hj : j ≠ Fin.last n := by
      intro heq
      subst j
      exact hk (le_antisymm (Fin.le_last k) hjk)
    simpa [Function.update, hj, hk] using hf hjk

namespace SurgeryParameterPrefix

variable {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) (Q : SurgeryNoncollapseExtension.{u} p)
    (R : SurgeryCanonicalExtension p Q)

theorem nextPrefix_deltaNext_le_last : R.deltaNext ≤ p.Delta (Fin.last p.i) :=
  R.delta_le_cutoff.trans (Q.cutoff_bounds R.rNext R.r_pos R.r_le_last).2

noncomputable def nextPrefix : SurgeryParameterPrefix K where
  setup := p.setup
  i := p.i + 1
  i_pos := Nat.succ_pos _
  r := Fin.snoc p.r R.rNext
  kappa := Fin.snoc p.kappa Q.kappaNew
  Delta := Fin.snoc
    (Function.update p.Delta (Fin.last p.i) R.deltaNext) R.deltaNext
  r_pos := by
    intro j
    cases j using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using R.r_pos
    | cast j => simpa only [Fin.snoc_castSucc] using p.r_pos j
  kappa_pos := by
    intro j
    cases j using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using Q.kappa_pos
    | cast j => simpa only [Fin.snoc_castSucc] using p.kappa_pos j
  Delta_pos := by
    intro j
    cases j using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using R.delta_pos
    | cast j =>
        by_cases hj : j = Fin.last p.i
        · subst j
          simpa using R.delta_pos
        · simpa [Function.update, hj] using p.Delta_pos j
  r_antitone := antitone_snoc_of_le_last p.r_antitone R.r_le_last
  kappa_antitone := antitone_snoc_of_le_last p.kappa_antitone Q.kappa_le_last
  Delta_antitone := antitone_snoc_of_le_last
    (antitone_update_last_of_le p.Delta_antitone (p.nextPrefix_deltaNext_le_last Q R))
    (by simp)
  r_zero := by
    change Fin.snoc (α := fun _ => ℝ) p.r R.rNext
      (0 : Fin (p.i + 1 + 1)) = p.setup.epsilon
    rw [Fin.snoc_apply_zero]
    exact p.r_zero
  r_le_epsilon := by
    intro j
    cases j using Fin.lastCases with
    | last =>
        simpa only [Fin.snoc_last] using
          R.r_le_last.trans (p.r_le_epsilon (Fin.last p.i))
    | cast j => simpa only [Fin.snoc_castSucc] using p.r_le_epsilon j
  Delta_le_setup := by
    have hdelta : R.deltaNext ≤ K.delta₀ :=
      (p.nextPrefix_deltaNext_le_last Q R).trans (p.Delta_le_setup (Fin.last p.i))
    intro j
    cases j using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hdelta
    | cast j =>
        by_cases hj : j = Fin.last p.i
        · subst j
          simpa using hdelta
        · simpa [Function.update, hj] using p.Delta_le_setup j

@[simp] theorem nextPrefix_setup : (p.nextPrefix Q R).setup = p.setup := rfl

@[simp] theorem nextPrefix_i : (p.nextPrefix Q R).i = p.i + 1 := rfl

@[simp] theorem nextPrefix_r_castSucc (j : Fin (p.i + 1)) :
    (p.nextPrefix Q R).r j.castSucc = p.r j := by
  change Fin.snoc (α := fun _ => ℝ) p.r R.rNext j.castSucc = p.r j
  exact Fin.snoc_castSucc (α := fun _ => ℝ) R.rNext p.r j

@[simp] theorem nextPrefix_kappa_castSucc (j : Fin (p.i + 1)) :
    (p.nextPrefix Q R).kappa j.castSucc = p.kappa j := by
  change Fin.snoc (α := fun _ => ℝ) p.kappa Q.kappaNew j.castSucc = p.kappa j
  exact Fin.snoc_castSucc (α := fun _ => ℝ) Q.kappaNew p.kappa j

theorem nextPrefix_Delta_castSucc (j : Fin (p.i + 1)) :
    (p.nextPrefix Q R).Delta j.castSucc =
      Function.update p.Delta (Fin.last p.i) R.deltaNext j := by
  change Fin.snoc (α := fun _ => ℝ)
    (Function.update p.Delta (Fin.last p.i) R.deltaNext)
    R.deltaNext j.castSucc = _
  exact Fin.snoc_castSucc (α := fun _ => ℝ) R.deltaNext _ j

theorem nextPrefix_Delta_castSucc_of_lt (j : Fin (p.i + 1)) (hj : j.val < p.i) :
    (p.nextPrefix Q R).Delta j.castSucc = p.Delta j := by
  have hne : j ≠ Fin.last p.i := by
    intro heq
    have hval := congrArg Fin.val heq
    exact (Nat.ne_of_lt hj) hval
  simp [nextPrefix_Delta_castSucc, Function.update, hne]

@[simp] theorem nextPrefix_Delta_penultimate :
    (p.nextPrefix Q R).Delta (Fin.last p.i).castSucc = R.deltaNext := by
  simp [nextPrefix_Delta_castSucc]

@[simp] theorem nextPrefix_r_last :
    (p.nextPrefix Q R).r (Fin.last (p.i + 1)) = R.rNext := by
  change Fin.snoc (α := fun _ => ℝ) p.r R.rNext (Fin.last (p.i + 1)) = R.rNext
  exact Fin.snoc_last (α := fun _ => ℝ) R.rNext p.r

@[simp] theorem nextPrefix_kappa_last :
    (p.nextPrefix Q R).kappa (Fin.last (p.i + 1)) = Q.kappaNew := by
  change Fin.snoc (α := fun _ => ℝ) p.kappa Q.kappaNew
    (Fin.last (p.i + 1)) = Q.kappaNew
  exact Fin.snoc_last (α := fun _ => ℝ) Q.kappaNew p.kappa

@[simp] theorem nextPrefix_Delta_last :
    (p.nextPrefix Q R).Delta (Fin.last (p.i + 1)) = R.deltaNext := by
  change Fin.snoc (α := fun _ => ℝ)
    (Function.update p.Delta (Fin.last p.i) R.deltaNext)
    R.deltaNext (Fin.last (p.i + 1)) = R.deltaNext
  exact Fin.snoc_last (α := fun _ => ℝ) R.deltaNext _

theorem nextPrefix_Delta_castSucc_le (j : Fin (p.i + 1)) :
    (p.nextPrefix Q R).Delta j.castSucc ≤ p.Delta j := by
  by_cases hj : j = Fin.last p.i
  · subst j
    simpa using p.nextPrefix_deltaNext_le_last Q R
  · simp [nextPrefix_Delta_castSucc, Function.update, hj]

@[simp] theorem nextPrefix_r_zero : (p.nextPrefix Q R).r 0 = p.r 0 := by
  change Fin.snoc (α := fun _ => ℝ) p.r R.rNext
    (0 : Fin (p.i + 1 + 1)) = p.r 0
  exact Fin.snoc_apply_zero (α := fun _ => ℝ) R.rNext p.r

@[simp] theorem nextPrefix_kappa_zero :
    (p.nextPrefix Q R).kappa 0 = p.kappa 0 := by
  change Fin.snoc (α := fun _ => ℝ) p.kappa Q.kappaNew
    (0 : Fin (p.i + 1 + 1)) = p.kappa 0
  exact Fin.snoc_apply_zero (α := fun _ => ℝ) Q.kappaNew p.kappa

@[simp] theorem nextPrefix_Delta_zero : (p.nextPrefix Q R).Delta 0 = p.Delta 0 := by
  change Fin.snoc (α := fun _ => ℝ)
    (Function.update p.Delta (Fin.last p.i) R.deltaNext) R.deltaNext
    (0 : Fin (p.i + 1 + 1)) = p.Delta 0
  rw [Fin.snoc_apply_zero]
  have hne : (0 : Fin (p.i + 1)) ≠ Fin.last p.i := by
    intro heq
    exact (Nat.ne_of_lt p.i_pos) (congrArg Fin.val heq)
  simp [Function.update, hne]

end SurgeryParameterPrefix

end PoincareConjecture
