import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.PartialSups
import Mathlib.Tactic.NormNum

/-!
# A monotone selection from positive local height intervals

The numerical argument in Morgan--Tian Corollary 11.36, printed p. 292,
uses finite prefix minima on a dyadic grid. The least eligible index replaces
the printed largest index (`MT-11.36-SELECTOR-INDEX`). The predicate is arbitrary;
its geometric downward-height property is an explicit input.

Mathlib's `partialSups` on the order dual provides the finite prefix minima,
and `Nat.find` provides the least eligible index.
-/

set_option autoImplicit false

namespace PoincareMT.M32

/-- A property valid on a positive interval of heights at every positive
parameter pair admits a positive selector monotone in both parameters.
This is the numerical part of Corollary 11.36, p. 292; the output is zero
outside the positive quadrant. -/
theorem exists_monotone_height_selection (Good : ℝ → ℝ → ℝ → Prop)
    (hmono : ∀ {r d r' d' a : ℝ}, 0 < r → 0 < d →
      r ≤ r' → d ≤ d' → Good r d a → Good r' d' a)
    (hlocal : ∀ r d : ℝ, 0 < r → 0 < d →
      ∃ b : ℝ, 0 < b ∧ ∀ a : ℝ, 0 < a → a ≤ b → Good r d a) :
    ∃ h : ℝ → ℝ → ℝ,
      (∀ r d, 0 < r → 0 < d → 0 < h r d) ∧
      (∀ d, Monotone (fun r => h r d)) ∧
      (∀ r, Monotone (h r)) ∧
      (∀ r d a, 0 < r → 0 < d → 0 < a → a ≤ h r d → Good r d a) := by
  classical
  let dyadic (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
  have hdyadic (n : ℕ) : 0 < dyadic n := pow_pos (by norm_num) n
  choose b hb hgood using fun n =>
    hlocal (dyadic n) (dyadic n) (hdyadic n) (hdyadic n)
  let c (n : ℕ) : ℝ := partialSups (α := ℝᵒᵈ) b n
  have hc (n : ℕ) : 0 < c n := by
    apply (partialSups_iff_forall (α := ℝᵒᵈ) (fun x : ℝ => 0 < x)
      (fun {_ _} => lt_min_iff)).2
    exact fun j _ => hb j
  have hcb (n : ℕ) : c n ≤ b n := le_partialSups (α := ℝᵒᵈ) b n
  have hcanti : Antitone c := (partialSups (α := ℝᵒᵈ) b).monotone
  have eligible {r d : ℝ} (hr : 0 < r) (hd : 0 < d) :
      ∃ n : ℕ, dyadic n ≤ r ∧ dyadic n ≤ d := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (lt_min hr hd)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, (hn.trans_le (min_le_left _ _)).le,
      (hn.trans_le (min_le_right _ _)).le⟩
  let index (r d : ℝ) (hp : 0 < r ∧ 0 < d) : ℕ :=
    Nat.find (eligible hp.1 hp.2)
  let h (r d : ℝ) : ℝ := if hp : 0 < r ∧ 0 < d then c (index r d hp) else 0
  have hnonneg (r d : ℝ) : 0 ≤ h r d := by
    dsimp only [h]
    split_ifs with hp
    · exact (hc _).le
    · exact le_rfl
  have hmonotone {r d r' d' : ℝ} (hrr : r ≤ r') (hdd : d ≤ d') :
      h r d ≤ h r' d' := by
    by_cases hp : 0 < r ∧ 0 < d
    · have hp' : 0 < r' ∧ 0 < d' := ⟨hp.1.trans_le hrr, hp.2.trans_le hdd⟩
      dsimp only [h]
      rw [dif_pos hp, dif_pos hp']
      apply hcanti
      exact Nat.find_mono (fun n hn => ⟨hn.1.trans hrr, hn.2.trans hdd⟩)
    · simpa only [h, dif_neg hp] using hnonneg r' d'
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · intro r d hr hd
    have hp : 0 < r ∧ 0 < d := ⟨hr, hd⟩
    simpa only [h, dif_pos hp] using hc (index r d hp)
  · intro d r r' hrr
    exact hmonotone hrr le_rfl
  · intro r d d' hdd
    exact hmonotone le_rfl hdd
  · intro r d a hr hd ha hle
    let n := index r d ⟨hr, hd⟩
    have hn : dyadic n ≤ r ∧ dyadic n ≤ d := Nat.find_spec (eligible hr hd)
    have hp : 0 < r ∧ 0 < d := ⟨hr, hd⟩
    have hac : a ≤ c n := by simpa only [h, dif_pos hp] using hle
    exact hmono (hdyadic n) (hdyadic n) hn.1 hn.2
      (hgood n a ha (hac.trans (hcb n)))

end PoincareMT.M32
