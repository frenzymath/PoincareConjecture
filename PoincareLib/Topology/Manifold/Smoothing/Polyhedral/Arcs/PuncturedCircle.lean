import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.IntermediateValue

/-!
# Connected punctured circles

The quotient image of an open interval of one positive period
is the complement of its endpoint class. This proves the
punctured-circle fact needed for Alexander's exceptional curves,
p. 7; see M76 derivation 151.
-/

set_option autoImplicit false

open Set

/-- Removing any point of a positive-period additive circle
leaves a nonempty connected set. See Alexander p. 7 and M76
derivation 151. -/
theorem AddCircle.isConnected_compl_singleton {p : ℝ} [Fact (0 < p)] (x : AddCircle p) :
    IsConnected ({x}ᶜ : Set (AddCircle p)) := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    let e := AddCircle.openPartialHomeomorphCoe p a
    change IsConnected e.target
    rw [← e.image_source_eq_target]
    exact (isConnected_Ioo (lt_add_of_pos_right a (Fact.out : 0 < p))).image
      e e.continuousOn

/-- The complement of any point on the unit circle is connected
and nonempty. See Alexander p. 7 and M76 derivation 151. -/
theorem Circle.isConnected_compl_singleton (q : Circle) :
    IsConnected ({q}ᶜ : Set Circle) := by
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  have h := (AddCircle.isConnected_compl_singleton (e.symm q)).image e
    e.continuous.continuousOn
  rwa [e.image_compl, image_singleton, e.apply_symm_apply] at h
