import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderRecursiveInduction

/-!
# Recentering a complete profile at its actual selected plane

Subtracting a selected height changes neither the carrier nor the
complete total charge. The real-height support is translated by an exact
bijection. See Alexander 1924, pp. 6--8 and M76 derivation 269.
-/

set_option autoImplicit false

open Set

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Recenter the same literal carrier and complete section profile at
height c. This supplies zero-centered local surgery without asserting
new geometric admissibility. See Alexander pp. 6--8 and derivation 269. -/
def recenter (P : AlexanderSectionProfile E) (c : ℝ) : AlexanderSectionProfile E where
  carrier := P.carrier
  height := P.height - AffineMap.const ℝ E c
  charge := fun d => P.charge (d + c)
  presentation d := by
    change HasAlexanderCurvePresentation
      (P.carrier ∩ {x | P.height x - c = d}) (P.charge (d + c))
    simpa only [sub_eq_iff_eq_add] using P.presentation (d + c)
  finite_support := by
    change ((fun d : ℝ => d + c) ⁻¹' Function.support P.charge).Finite
    exact P.finite_support.preimage (fun _ _ _ _ h => add_right_cancel h)

/-- Recentering retains the literal carrier. See derivation 269. -/
@[simp] theorem recenter_carrier (P : AlexanderSectionProfile E) (c : ℝ) :
    (P.recenter c).carrier = P.carrier := rfl

/-- The recentered affine height subtracts exactly c.
See Alexander p. 7 and derivation 269. -/
@[simp] theorem recenter_height_apply (P : AlexanderSectionProfile E) (c : ℝ) (x : E) :
    (P.recenter c).height x = P.height x - c := rfl

/-- Every recentered charge is the original charge at the corresponding
real height. See Alexander pp. 6--8 and derivation 269. -/
@[simp] theorem recenter_charge_apply (P : AlexanderSectionProfile E) (c d : ℝ) :
    (P.recenter c).charge d = P.charge (d + c) := rfl

/-- The total actual charge is unchanged by recentering at any real
height. The proof reindexes the profiles' own finite supports, without
choosing another event set. See Alexander p. 7 and derivation 269. -/
@[simp] theorem complexity_recenter (P : AlexanderSectionProfile E) (c : ℝ) :
    (P.recenter c).complexity = P.complexity := by
  classical
  unfold complexity
  refine Finset.sum_bij (fun d _ => d + c) ?_ ?_ ?_ ?_
  · intro d hd
    exact P.finite_support.mem_toFinset.mpr
      ((P.recenter c).finite_support.mem_toFinset.mp hd)
  · intro d _ e _ h
    exact add_right_cancel h
  · intro d hd
    have hmem : d - c ∈ (P.recenter c).finite_support.toFinset := by
      apply (P.recenter c).finite_support.mem_toFinset.mpr
      change P.charge (d - c + c) ≠ 0
      simpa only [sub_add_cancel, Function.mem_support] using P.finite_support.mem_toFinset.mp hd
    exact ⟨d - c, hmem, sub_add_cancel d c⟩
  · exact fun _ _ => rfl

end Geometry.AlexanderSectionProfile
