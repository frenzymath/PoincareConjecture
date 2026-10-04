import PoincareLib.AlgebraicTopology.SingularHomology.Relative.IntegralFiniteSupport

/-!
# Actual homology restrictions to two distinct points

Closed-support Mayer--Vietoris identifies homology supported at two
distinct points with the product of their local groups, through the
actual restrictions. Empty-support vanishing gives both gluing and
uniqueness. Source: Hatcher, pp. 149-150, and M53 derivation 08, for the
separation repair of Morgan--Tian, Proposition 15.12 and Remark 15.13,
p. 365.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open Poincare.Topology

universe u

namespace PoincareMT.Topology.EmbeddedSphere

/-- Two distinct point supports have independent local homology
coordinates, given by the canonical restrictions in every degree.
Source: Hatcher, pp. 149-150, and M53 derivation 08. -/
theorem integralSupportHomology_twoPoint_bijective
    {X : Type u} [TopologicalSpace X] [T1Space X] (x y : X) (hxy : x ≠ y) (n : Nat) :
    Function.Bijective (fun a : integralSupportHomology ({x} ∪ {y}) n =>
      (integralSupportHomologyRestriction
        (Set.subset_union_left : ({x} : Set X) ⊆ {x} ∪ {y}) n a,
        integralSupportHomologyRestriction
          (Set.subset_union_right : ({y} : Set X) ⊆ {x} ∪ {y}) n a)) := by
  have hinter : ({x} : Set X) ∩ {y} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hxy (hz.1.symm.trans hz.2)
  have hI (k : Nat) : IsZero (integralSupportHomology (({x} : Set X) ∩ {y}) k) := by
    rw [hinter]
    exact integralSupportHomology_empty_isZero k
  constructor
  · intro a b hab
    exact integralSupportHomology_union_ext {x} {y} isClosed_singleton isClosed_singleton n
      (hI (n + 1)) (congrArg Prod.fst hab) (congrArg Prod.snd hab)
  · rintro ⟨a, b⟩
    obtain ⟨c, hc₁, hc₂⟩ := exists_integralSupportHomology_union {x} {y}
      isClosed_singleton isClosed_singleton n a b
      ((ModuleCat.isZero_iff_subsingleton.mp (hI n)).elim _ _)
    exact ⟨c, Prod.ext hc₁ hc₂⟩

end PoincareMT.Topology.EmbeddedSphere
