import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set

namespace PoincareConjecture

theorem m64Dirichlet_nonnegative_potential_eq_zero
    {a b : ℝ} {f v q : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hfv : ∀ x ∈ Ioo a b, HasDerivAt f (v x) x)
    (hvq : ∀ x ∈ Ioo a b, HasDerivAt v (q x * f x) x)
    (hq : ∀ x ∈ Ioo a b, 0 ≤ q x) (ha : f a = 0) (hb : f b = 0) :
    EqOn f (fun _ => 0) (Icc a b) := by
  have hfirst (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun t => f t ^ 2) (2 * (f x * v x)) x := by
    have hd : HasDerivAt (fun t => f t * f t) (v x * f x + f x * v x) x :=
      (hfv x hx).mul (hfv x hx)
    have heq : v x * f x + f x * v x = 2 * (f x * v x) := by ring
    simpa only [heq, pow_two] using hd
  have hsecond (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun t => 2 * (f t * v t))
        (2 * (v x ^ 2 + q x * f x ^ 2)) x := by
    have hd : HasDerivAt (fun t => 2 * (f t * v t))
        (2 * (v x * v x + f x * (q x * f x))) x :=
      ((hfv x hx).mul (hvq x hx)).const_mul 2
    convert hd using 1
    ring
  have hconv : ConvexOn ℝ (Icc a b) (fun x => f x ^ 2) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b) (hf.pow 2)
      (f' := fun x => 2 * (f x * v x))
      (f'' := fun x => 2 * (v x ^ 2 + q x * f x ^ 2))
    · intro x hx
      exact (hfirst x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      exact (hsecond x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      have hqx := hq x (by simpa only [interior_Icc] using hx)
      positivity
  intro x hx
  have hab := hx.1.trans hx.2
  have hle := hconv.le_max_of_mem_Icc (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hx
  simp only [ha, hb, zero_pow (by decide : 2 ≠ 0), max_self] at hle
  exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))

end PoincareConjecture
