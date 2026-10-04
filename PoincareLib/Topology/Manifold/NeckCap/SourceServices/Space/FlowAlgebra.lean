import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Space.BoundedFlow
import Mathlib.Topology.Algebra.Support

/-!
# Algebra and support of a bounded autonomous flow

Uniqueness gives the flow composition law, inverse time maps, and fixed
points wherever the field vanishes. These are prerequisites for the
restricted ambient isotopies used in Hatcher, Notes on Basic 3-Manifold
Topology, Theorem 1.1 and Lemmas 1.2-1.3, pp. 1-3.

Joint smoothness is established separately, not assumed by this file.
-/

set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (f : E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)

/-- The uniquely determined global curve starting at `x` for the bounded
Lipschitz field `f`; see the bounded-flow derivation of 2026-09-21. -/
noncomputable def boundedFlow (x : E) (t : ℝ) : E :=
  Classical.choose (boundedField_globalSolution f hK hL x) t

/-- The selected global flow takes the prescribed initial value. -/
@[simp] theorem boundedFlow_zero (x : E) : boundedFlow f hK hL x 0 = x :=
  (Classical.choose_spec (boundedField_globalSolution f hK hL x)).1

/-- Every selected global curve solves the vector-field equation. -/
theorem boundedFlow_hasDerivAt (x : E) (t : ℝ) :
    HasDerivAt (boundedFlow f hK hL x) (f (boundedFlow f hK hL x t)) t :=
  (Classical.choose_spec (boundedField_globalSolution f hK hL x)).2 t

/-- Flowing for `s` and then for `t` equals flowing for `s + t`.
This is a consequence of ODE uniqueness, not an extra flow axiom. -/
theorem boundedFlow_add (x : E) (s t : ℝ) :
    boundedFlow f hK hL x (s + t) =
      boundedFlow f hK hL (boundedFlow f hK hL x s) t := by
  have hshift (u : ℝ) :
      HasDerivAt (fun v => boundedFlow f hK hL x (s + v))
        (f (boundedFlow f hK hL x (s + u))) u := by
    simpa only [Function.comp_def, one_smul] using
      (boundedFlow_hasDerivAt f hK hL x (s + u)).scomp u
        ((hasDerivAt_id u).const_add s)
  have heq := boundedField_solution_unique f hK hshift
    (boundedFlow_hasDerivAt f hK hL (boundedFlow f hK hL x s))
    (by simp only [add_zero, boundedFlow_zero])
  exact congrFun heq t

/-- Negative time reverses the flow. -/
@[simp] theorem boundedFlow_neg (x : E) (t : ℝ) :
    boundedFlow f hK hL (boundedFlow f hK hL x t) (-t) = x := by
  rw [← boundedFlow_add, add_neg_cancel, boundedFlow_zero]

/-- Each fixed-time map is a set equivalence, with inverse at negative
time. Its smoothness is proved in the subsequent flow-regularity stage. -/
noncomputable def boundedFlowEquiv (t : ℝ) : E ≃ E where
  toFun x := boundedFlow f hK hL x t
  invFun x := boundedFlow f hK hL x (-t)
  left_inv x := boundedFlow_neg f hK hL x t
  right_inv x := by
    simpa only [neg_neg] using boundedFlow_neg f hK hL x (-t)

/-- A fixed-time flow map is injective. -/
theorem boundedFlow_injective (t : ℝ) :
    Function.Injective (fun x => boundedFlow f hK hL x t) :=
  (boundedFlowEquiv f hK hL t).injective

/-- A fixed-time flow map is surjective. -/
theorem boundedFlow_surjective (t : ℝ) :
    Function.Surjective (fun x => boundedFlow f hK hL x t) :=
  (boundedFlowEquiv f hK hL t).surjective

/-- A zero of the vector field is fixed for all time, by uniqueness
against the constant integral curve. -/
theorem boundedFlow_eq_self (x : E) (hx : f x = 0) (t : ℝ) :
    boundedFlow f hK hL x t = x := by
  have hconst (u : ℝ) : HasDerivAt (fun _ : ℝ => x) (f x) u := by
    rw [hx]
    exact hasDerivAt_const u x
  have heq := boundedField_solution_unique f hK
    (boundedFlow_hasDerivAt f hK hL x) hconst (boundedFlow_zero f hK hL x)
  exact congrFun heq t

/-- The displacement of a flow is supported where the field is nonzero. -/
theorem boundedFlow_support_subset (t : ℝ) :
    Function.support (fun x => boundedFlow f hK hL x t - x) ⊆ Function.support f := by
  intro x hx
  by_contra hfx
  have heq : f x = 0 := Function.notMem_support.mp hfx
  exact hx (sub_eq_zero.mpr (boundedFlow_eq_self f hK hL x heq t))

/-- A compactly supported vector field has compactly supported flow
displacement at every fixed time. -/
theorem boundedFlow_hasCompactSupport (hf : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (fun x => boundedFlow f hK hL x t - x) :=
  hf.mono (boundedFlow_support_subset f hK hL t)

end PoincareMT.M25.Topology3D
