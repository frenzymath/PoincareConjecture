import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A bad point controlling all earlier points above twice its value

A bounded nonempty set of bad values has a point above half its
supremum. Transitivity of an arbitrary preorder clock then excludes
earlier bad points with twice that value. No maximum is required.
Source: the point selection in Morgan-Tian Theorem 12.28, pp. 323-324;
M34 bad-point selection derivation, section 2.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M34

/-- A positive bad seed and an upper bound on earlier bad values give
a bad point with all earlier sufficiently high points good. -/
theorem exists_bad_point_with_earlier_good
    {X T : Type*} [Preorder T] (time : X → T) (value : X → ℝ) (Good : X → Prop)
    (p0 : X) (hbad : ¬ Good p0) (hpositive : 0 < value p0)
    (hbound : BddAbove (value '' {p | time p ≤ time p0 ∧ ¬ Good p})) :
    ∃ p : X, time p ≤ time p0 ∧ ¬ Good p ∧ value p0 / 2 < value p ∧
      ∀ q : X, time q ≤ time p → 2 * value p ≤ value q → Good q := by
  classical
  let V := value '' {p | time p ≤ time p0 ∧ ¬ Good p}
  have hseed : value p0 ∈ V := ⟨p0, ⟨le_rfl, hbad⟩, rfl⟩
  have hsup : value p0 ≤ sSup V := le_csSup hbound hseed
  have hhalf : sSup V / 2 < sSup V := by linarith
  obtain ⟨a, ⟨p, ⟨ht, hp⟩, rfl⟩, ha⟩ := exists_lt_of_lt_csSup ⟨value p0, hseed⟩ hhalf
  refine ⟨p, ht, hp, by linarith, ?_⟩
  intro q hq hv
  by_contra hbadq
  have hqbound : value q ≤ sSup V :=
    le_csSup hbound ⟨q, ⟨hq.trans ht, hbadq⟩, rfl⟩
  linarith

end PoincareMT.M34
