import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTrianglePointwiseGluing

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E)

abbrev fiberTriangle (z : E) :=
  {s : Triangle K // z ∈ convexHull ℝ (s.val : Set E)}

def fiberCopy (label : Triangle K → ℝ) (z : E) (s : fiberTriangle K z) :
    carrier K label :=
  ⟨(z, label s.val), mem_iUnion.mpr
    ⟨s.val, (mem_copy_iff K label s.val _).mpr ⟨s.property, rfl⟩⟩⟩

omit [FiniteDimensional ℝ E] in
private theorem copy_owner_unique (label : Triangle K → ℝ)
    (hi : Function.Injective label) {x : E × ℝ} {s t : Triangle K}
    (hs : x ∈ copy K label s) (ht : x ∈ copy K label t) : s = t :=
  hi (((mem_copy_iff K label s x).mp hs).2.symm.trans
    ((mem_copy_iff K label t x).mp ht).2)

theorem pointwiseGlueRelation_fiberChain
    (label : Triangle K → ℝ) (hi : Function.Injective label)
    (contact : Triangle K → Triangle K → Prop)
    {x y : carrier K label} (hxy : pointwiseGlueRelation K label contact x y)
    {z : E} (hz : x.val.1 = z) {s t : fiberTriangle K z}
    (hs : x.val ∈ copy K label s.val) (ht : y.val ∈ copy K label t.val) :
    Relation.EqvGen (fun a b : fiberTriangle K z => contact a.val b.val) s t := by
  induction hxy using Relation.EqvGen.rec generalizing z with
  | rel x y h =>
      obtain ⟨a, b, ha, hb, hab, _⟩ := h
      have has := copy_owner_unique K label hi ha hs
      have hbt := copy_owner_unique K label hi hb ht
      exact Relation.EqvGen.rel s t (has ▸ hbt ▸ hab)
  | refl x =>
      have hst : s = t := Subtype.ext (copy_owner_unique K label hi hs ht)
      subst t
      exact Relation.EqvGen.refl s
  | symm x y h ih =>
      have hyz : x.val.1 = z := (pointwiseGlueRelation_fiber K label contact h).trans hz
      exact (ih hyz ht hs).symm
  | trans x y w hxy hyw ihxy ihyw =>
      obtain ⟨a, ha⟩ := mem_iUnion.mp y.property
      have hyz : y.val.1 = z :=
        (pointwiseGlueRelation_fiber K label contact hxy).symm.trans hz
      let m : fiberTriangle K z :=
        ⟨a, hyz ▸ ((mem_copy_iff K label a y.val).mp ha).1⟩
      exact Relation.EqvGen.trans s m t (ihxy hz hs ha) (ihyw hyz ha ht)

omit [FiniteDimensional ℝ E] in
theorem fiberChain_pointwiseGlueRelation
    (label : Triangle K → ℝ) (contact : Triangle K → Triangle K → Prop)
    {z : E} {s t : fiberTriangle K z}
    (h : Relation.EqvGen (fun a b : fiberTriangle K z => contact a.val b.val) s t) :
    pointwiseGlueRelation K label contact (fiberCopy K label z s) (fiberCopy K label z t) := by
  induction h with
  | rel a b hab =>
      apply Relation.EqvGen.rel
      exact ⟨a.val, b.val,
        (mem_copy_iff K label a.val _).mpr ⟨a.property, rfl⟩,
        (mem_copy_iff K label b.val _).mpr ⟨b.property, rfl⟩, hab, rfl⟩
  | refl a => exact Relation.EqvGen.refl _
  | symm a b h ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc

theorem fiberCopy_glue_iff
    (label : Triangle K → ℝ) (hi : Function.Injective label)
    (contact : Triangle K → Triangle K → Prop)
    {z : E} (s t : fiberTriangle K z) :
    pointwiseGlueRelation K label contact (fiberCopy K label z s) (fiberCopy K label z t) ↔
      Relation.EqvGen (fun a b : fiberTriangle K z => contact a.val b.val) s t := by
  constructor
  · intro h
    exact pointwiseGlueRelation_fiberChain K label hi contact h rfl
      ((mem_copy_iff K label s.val _).mpr ⟨s.property, rfl⟩)
      ((mem_copy_iff K label t.val _).mpr ⟨t.property, rfl⟩)
  · exact fiberChain_pointwiseGlueRelation K label contact

end PoincareConjecture.M76.OriginalTriangleCopies
