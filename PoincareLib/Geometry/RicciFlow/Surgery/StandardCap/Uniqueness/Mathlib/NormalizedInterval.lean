import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith

/-!
# An affine backward interval inclusion

The real-variable interval calculation used in Morgan-Tian, Theorem 12.28,
pp. 323-324, when realizing finite normalized past intervals of the actual flow.
-/

set_option autoImplicit false

open Set

/-- A finite normalized past remains in the original half-open time interval.
Used in Theorem 12.28, pp. 323-324. -/
theorem add_div_mem_Ico_of_mem_Icc {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] {L a Q T s : 𝕜} (ha : a ∈ Ico 0 L)
    (hQ : 0 < Q) (hT : T ≤ Q * a) (hs : s ∈ Icc (-T) 0) :
    a + s / Q ∈ Ico 0 L := by
  have hlo : -a ≤ s / Q := (le_div_iff₀ hQ).2 (by nlinarith [hs.1])
  have hhi : s / Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le
  exact ⟨by linarith, by linarith [ha.2]⟩
