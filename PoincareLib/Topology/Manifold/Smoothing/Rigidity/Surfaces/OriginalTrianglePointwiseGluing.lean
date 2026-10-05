import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTriangleSideGluing

/-!
# Pointwise gluing of copied triangles

The side relation in `OriginalTriangleSideGluing` first closes the contact
relation on triangle labels.  That is too coarse when two different contact
chains can meet the same original point: every generator must retain the
pointwise equality in `E`.  This file therefore closes the relation on copied
carrier points themselves.  A chain can only move through copies containing
the same original point.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)

variable [FiniteDimensional ℝ E]

/-- One pointwise contact step between two separated triangle copies. -/
def pointwiseGlueGenerator (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop)
    (x y : carrier K label) : Prop :=
  ∃ s t : Triangle K,
    x.1 ∈ copy K label s ∧ y.1 ∈ copy K label t ∧
      contact s t ∧ x.1.1 = y.1.1

/-- The corrected gluing relation, closed on carrier points rather than labels. -/
def pointwiseGlueRelation (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop) :
    carrier K label → carrier K label → Prop :=
  Relation.EqvGen (pointwiseGlueGenerator K label contact)

/-- Pointwise gluing is the canonical equivalence closure of its generators. -/
def pointwiseGlueSetoid (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop) : Setoid (carrier K label) :=
  Relation.EqvGen.setoid (pointwiseGlueGenerator K label contact)

theorem pointwiseGlueRelation_refl (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop) (x : carrier K label) :
    pointwiseGlueRelation K label contact x x :=
  Relation.EqvGen.refl x

theorem pointwiseGlueRelation_symm (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop) {x y : carrier K label}
    (hxy : pointwiseGlueRelation K label contact x y) :
    pointwiseGlueRelation K label contact y x :=
  Relation.EqvGen.symm x y hxy

theorem pointwiseGlueRelation_trans (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop) {x y z : carrier K label}
    (hxy : pointwiseGlueRelation K label contact x y)
    (hyz : pointwiseGlueRelation K label contact y z) :
    pointwiseGlueRelation K label contact x z :=
  Relation.EqvGen.trans x y z hxy hyz

theorem pointwiseGlueRelation_generator_fiber
    (label : Triangle K → ℝ) (contact : Triangle K → Triangle K → Prop)
    {x y : carrier K label}
    (hxy : pointwiseGlueGenerator K label contact x y) :
    x.1.1 = y.1.1 := by
  rcases hxy with ⟨s, t, hs, ht, hcontact, hcoord⟩
  exact hcoord

theorem pointwiseGlueRelation_fiber (label : Triangle K → ℝ)
    (contact : Triangle K → Triangle K → Prop)
    {x y : carrier K label}
    (hxy : pointwiseGlueRelation K label contact x y) :
    x.1.1 = y.1.1 := by
  induction hxy using Relation.EqvGen.rec with
  | rel x y hxy => exact pointwiseGlueRelation_generator_fiber K label contact hxy
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

theorem pointwiseGlueRelation_le_sideGlueRelation
    (label : Triangle K → ℝ) (hi : Function.Injective label)
    (contact : Triangle K → Triangle K → Prop)
    {x y : carrier K label}
    (hxy : pointwiseGlueRelation K label contact x y) :
    sideGlueRelation K label contact x y := by
  induction hxy using Relation.EqvGen.rec with
  | rel x y hxy =>
      obtain ⟨s, t, hs, ht, hst, hcoord⟩ := hxy
      exact ⟨s, t, hs, ht, Relation.EqvGen.rel s t hst, hcoord⟩
  | refl x => exact sideGlueRelation_refl K label contact x
  | symm x y hxy ih => exact sideGlueRelation_symm K label contact ih
  | trans x y z hxy hyz ihxy ihyz =>
      exact sideGlueRelation_trans K label hi contact ihxy ihyz

end PoincareMT.M76.OriginalTriangleCopies
