import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundedFlow
import Mathlib.Topology.Algebra.Support












set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (f : E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)



noncomputable def boundedFlow (x : E) (t : ℝ) : E :=
  Classical.choose (boundedField_globalSolution f hK hL x) t


@[simp] theorem boundedFlow_zero (x : E) : boundedFlow f hK hL x 0 = x :=
  (Classical.choose_spec (boundedField_globalSolution f hK hL x)).1


theorem boundedFlow_hasDerivAt (x : E) (t : ℝ) :
    HasDerivAt (boundedFlow f hK hL x) (f (boundedFlow f hK hL x t)) t :=
  (Classical.choose_spec (boundedField_globalSolution f hK hL x)).2 t



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


@[simp] theorem boundedFlow_neg (x : E) (t : ℝ) :
    boundedFlow f hK hL (boundedFlow f hK hL x t) (-t) = x := by
  rw [← boundedFlow_add, add_neg_cancel, boundedFlow_zero]



noncomputable def boundedFlowEquiv (t : ℝ) : E ≃ E where
  toFun x := boundedFlow f hK hL x t
  invFun x := boundedFlow f hK hL x (-t)
  left_inv x := boundedFlow_neg f hK hL x t
  right_inv x := by
    simpa only [neg_neg] using boundedFlow_neg f hK hL x (-t)


theorem boundedFlow_injective (t : ℝ) :
    Function.Injective (fun x => boundedFlow f hK hL x t) :=
  (boundedFlowEquiv f hK hL t).injective


theorem boundedFlow_surjective (t : ℝ) :
    Function.Surjective (fun x => boundedFlow f hK hL x t) :=
  (boundedFlowEquiv f hK hL t).surjective



theorem boundedFlow_eq_self (x : E) (hx : f x = 0) (t : ℝ) :
    boundedFlow f hK hL x t = x := by
  have hconst (u : ℝ) : HasDerivAt (fun _ : ℝ => x) (f x) u := by
    rw [hx]
    exact hasDerivAt_const u x
  have heq := boundedField_solution_unique f hK
    (boundedFlow_hasDerivAt f hK hL x) hconst (boundedFlow_zero f hK hL x)
  exact congrFun heq t


theorem boundedFlow_support_subset (t : ℝ) :
    Function.support (fun x => boundedFlow f hK hL x t - x) ⊆ Function.support f := by
  intro x hx
  by_contra hfx
  have heq : f x = 0 := Function.notMem_support.mp hfx
  exact hx (sub_eq_zero.mpr (boundedFlow_eq_self f hK hL x heq t))



theorem boundedFlow_hasCompactSupport (hf : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (fun x => boundedFlow f hK hL x t - x) :=
  hf.mono (boundedFlow_support_subset f hK hL t)

end PoincareConjecture.M25.Topology3D
