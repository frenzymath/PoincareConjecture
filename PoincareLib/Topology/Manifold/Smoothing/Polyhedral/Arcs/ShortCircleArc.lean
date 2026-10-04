import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Short arcs of an additive circle

An interval of length at most half the period embeds isometrically in the
additive circle and is homeomorphic to its image. This is the elementary
short-geodesic fact used in Cairns 1940, Section 6, p. 802.
See M76 derivation 15. Empty intervals are allowed.
-/

set_option autoImplicit false

open Set

namespace AddCircle

variable {p a b : ℝ}

/-- The quotient onto a circle preserves distances on any interval of
length at most half the positive period. See Cairns p. 802 and
M76 derivation 15. -/
theorem isometry_coe_shortInterval (hp : 0 < p) (hab : b - a ≤ p / 2) :
    Isometry (fun x : Icc a b => (x.val : AddCircle p)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, Subtype.dist_eq, Real.dist_eq]
  apply (norm_coe_eq_abs_iff p hp.ne').mpr
  rw [abs_of_pos hp, abs_le]
  constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]

/-- A closed interval shorter than half the period has no quotient
identifications. See Cairns p. 802 and M76 derivation 15. -/
theorem injOn_coe_shortInterval (hp : 0 < p) (hab : b - a ≤ p / 2) :
    InjOn (fun x : ℝ => (x : AddCircle p)) (Icc a b) := by
  intro x hx y hy hxy
  exact congrArg Subtype.val
    ((isometry_coe_shortInterval hp hab).injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

/-- A short closed arc has its usual interval topology. The forward map
is reduction modulo the period. See Cairns p. 802 and M76 derivation 15. -/
noncomputable def shortArcHomeomorph (hp : 0 < p) (hab : b - a ≤ p / 2) :
    Icc a b ≃ₜ (fun x : ℝ => (x : AddCircle p)) '' Icc a b :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn _ _ (injOn_coe_shortInterval hp hab))
    ((AddCircle.continuous_mk' p).comp continuous_subtype_val |>.subtype_mk _)

/-- The short-arc homeomorphism is the usual quotient map.
See M76 derivation 15. -/
theorem shortArcHomeomorph_apply (hp : 0 < p) (hab : b - a ≤ p / 2) (x : Icc a b) :
    (shortArcHomeomorph hp hab x : AddCircle p) = (x.val : AddCircle p) := rfl

end AddCircle
