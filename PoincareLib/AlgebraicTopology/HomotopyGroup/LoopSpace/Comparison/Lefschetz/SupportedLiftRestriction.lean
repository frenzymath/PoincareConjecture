import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SupportedComparison

/-!
# Restricting the actual lifted model to a coordinate neighborhood

The subcomplex supported on a vertex set is the literal lifted model of
the supported characteristic simplices in the corresponding open
coordinate neighborhood. Both directions retain the actual singular
simplex, changing only its codomain subtype.
Source: Hatcher, Theorem 2.27, printed pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]
  {E : Type u} [TopologicalSpace E]
  (p : C(E, (finiteOrderComplex J).space)) (s : Finset J)

/-- The actual covering projection restricted to its coordinate
neighborhood. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def liftedCoordinateProjection :
    C(liftedCoordinateNeighborhood p s, orderComplexNeighborhood s) :=
  ⟨(orderComplexNeighborhood s).restrictPreimage p,
    (p.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The supported characteristic map retains its entire simplex inside
the selected coordinate neighborhood. Source: Hatcher, Theorem 2.27. -/
def orderComplexSupportedSingular : (supportedNerve s).toSSet ⟶
    TopCat.toSSet.obj (TopCat.of (orderComplexNeighborhood s)) :=
  singularMapOfContinuousSimplices _ _
    (fun _ z => ⟨fun t => ⟨orderComplexSimplex z.val t,
      orderComplexSimplex_mem_neighborhood s z t⟩,
      (orderComplexSimplex z.val).continuous.subtype_mk _⟩) (by
    intro n m f z
    ext t : 1
    apply Subtype.ext
    exact congrArg (fun g => g t) (orderComplexSimplex_comp f z.val))

set_option maxHeartbeats 1000000 in
-- The inverse laws reduce through three nested subtypes and singular adjunction maps.
/-- Restricting a supported singular lift is an actual simplicial
isomorphism with the lifted model of the restricted covering.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def supportedLiftRestrictionIso :
    (supportedSingularLift p (orderComplexSingular J) s).toSSet ≅
      singularLiftSSet (liftedCoordinateProjection p s)
        (supportedNerve s).toSSet (orderComplexSupportedSingular s) where
  hom := {
    app n := ↾fun z => ⟨(⟨z.val.val.1, z.property⟩,
      (supportedSingularComparison p s).app n z), by
        apply ((TopCat.of (orderComplexNeighborhood s)).toSSetObjEquiv n).injective
        ext t : 1
        apply Subtype.ext
        exact congrArg (fun a =>
          (TopCat.of (finiteOrderComplex J).space).toSSetObjEquiv n a t) z.val.property⟩
    naturality {n m} f := by
      apply ConcreteCategory.hom_ext
      intro z
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply ((TopCat.of (liftedCoordinateNeighborhood p s)).toSSetObjEquiv m).injective
        rfl }
  inv := {
    app n := ↾fun z => ⟨⟨(z.val.1.val,
      (TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C(liftedCoordinateNeighborhood p s, E)))).app n z.val.2), by
          apply ((TopCat.of (finiteOrderComplex J).space).toSSetObjEquiv n).injective
          ext t : 1
          exact congrArg (fun a =>
            ((TopCat.of (orderComplexNeighborhood s)).toSSetObjEquiv n a t).val)
              z.property⟩, z.val.1.property⟩
    naturality {n m} f := by
      apply ConcreteCategory.hom_ext
      intro z
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext rfl
      apply ((TopCat.of E).toSSetObjEquiv m).injective
      rfl }
  hom_inv_id := by
    ext n : 1
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext rfl
    apply ((TopCat.of E).toSSetObjEquiv n).injective
    rfl
  inv_hom_id := by
    ext n : 1
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    apply Prod.ext rfl
    apply ((TopCat.of (liftedCoordinateNeighborhood p s)).toSSetObjEquiv n).injective
    rfl

/-- The restriction isomorphism preserves the actual singular
characteristic map. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem supportedLiftRestrictionIso_projection :
    (supportedLiftRestrictionIso p s).hom ≫
      singularLiftProjection (liftedCoordinateProjection p s)
        (supportedNerve s).toSSet (orderComplexSupportedSingular s) =
      supportedSingularComparison p s := rfl

end PoincareMT.Proofs.M59
