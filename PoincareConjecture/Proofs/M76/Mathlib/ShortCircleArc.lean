import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Real










set_option autoImplicit false

open Set

namespace AddCircle

variable {p a b : ℝ}




theorem isometry_coe_shortInterval (hp : 0 < p) (hab : b - a ≤ p / 2) :
    Isometry (fun x : Icc a b => (x.val : AddCircle p)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, Subtype.dist_eq, Real.dist_eq]
  apply (norm_coe_eq_abs_iff p hp.ne').mpr
  rw [abs_of_pos hp, abs_le]
  constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]



theorem injOn_coe_shortInterval (hp : 0 < p) (hab : b - a ≤ p / 2) :
    InjOn (fun x : ℝ => (x : AddCircle p)) (Icc a b) := by
  intro x hx y hy hxy
  exact congrArg Subtype.val
    ((isometry_coe_shortInterval hp hab).injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)



noncomputable def shortArcHomeomorph (hp : 0 < p) (hab : b - a ≤ p / 2) :
    Icc a b ≃ₜ (fun x : ℝ => (x : AddCircle p)) '' Icc a b :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn _ _ (injOn_coe_shortInterval hp hab))
    ((AddCircle.continuous_mk' p).comp continuous_subtype_val |>.subtype_mk _)



theorem shortArcHomeomorph_apply (hp : 0 < p) (hab : b - a ≤ p / 2) (x : Icc a b) :
    (shortArcHomeomorph hp hab x : AddCircle p) = (x.val : AddCircle p) := rfl

end AddCircle
