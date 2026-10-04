import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Homotopy of slices of an interval-indexed continuous family

The topological step used for the projected family following Morgan--Tian
Claim 19.22, printed p. 453, and Proposition 18.24, printed p. 433.
The source and target are arbitrary topological spaces.
-/

set_option autoImplicit false

open scoped unitInterval

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Slices of a jointly continuous family over a real closed interval are
homotopic. The affine path stays in the interval, even if it is a singleton.
Used in Proposition 18.24, Morgan--Tian p. 433; see the M65 derivation
`01-profile-and-assembly.md`. -/
theorem homotopic_of_continuous_icc {a b : ℝ}
    (family : Set.Icc a b → C(X, Y))
    (hfamily : Continuous (fun p : Set.Icc a b × X => family p.1 p.2))
    (s t : Set.Icc a b) : (family s).Homotopic (family t) := by
  let time : I → Set.Icc a b := fun r =>
    ⟨(1 - (r : ℝ)) * s.1 + (r : ℝ) * t.1, by
      constructor
      · nlinarith [s.2.1, t.2.1, r.2.1, r.2.2,
          mul_nonneg (sub_nonneg.mpr r.2.2) (sub_nonneg.mpr s.2.1),
          mul_nonneg r.2.1 (sub_nonneg.mpr t.2.1)]
      · nlinarith [s.2.2, t.2.2, r.2.1, r.2.2,
          mul_nonneg (sub_nonneg.mpr r.2.2) (sub_nonneg.mpr s.2.2),
          mul_nonneg r.2.1 (sub_nonneg.mpr t.2.2)]⟩
  have htime : Continuous time := by fun_prop
  refine ⟨{
    toFun := fun p => family (time p.1) p.2
    continuous_toFun := hfamily.comp ((htime.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    have hzero : time 0 = s := by ext; simp [time]
    rw [hzero]
  · intro x
    have hone : time 1 = t := by ext; simp [time]
    rw [hone]

end ContinuousMap
