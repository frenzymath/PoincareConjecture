import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.TrivialLift
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.ConeSimplicial
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.ExtraDegeneracyChains
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology

/-!
# Cone comparison through the actual covering fiber

The product trivialization sends a lifted characteristic simplex to its
constant fiber label. That map is exactly the characteristic projection
followed by the topological fiber retraction and initial-vertex evaluation.
The cone extra degeneracy and the discrete singular isomorphism therefore
give the required quasi-isomorphism by two-out-of-three.
Source: Hatcher, Theorem 2.27, printed pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open scoped Simplicial MonoidalCategory

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J]
  (s : Finset J) (v : J) (hv : v ∈ s) (hmin : ∀ j ∈ s, v ≤ j)
  {E X F : Type u} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace F] [DiscreteTopology F]
  (p : C(E, X))
  (χ : (supportedNerve s).toSSet ⟶ TopCat.toSSet.obj (TopCat.of X))
  (e : E ≃ₜ X × F) (he : ∀ z, p z = (e z).1)

/-- The literal fiber coordinate of a product covering.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def coveringProductRetraction : C(E, F) :=
  ⟨fun z => (e z).2, continuous_snd.comp e.continuous⟩

/-- The cone augmentation retains exactly the fiber coordinate of the
original singular simplex. Source: Hatcher, Theorem 2.27. -/
theorem singularLiftCone_augmentation :
    (singularLiftTrivializationIso p (supportedNerve s).toSSet χ e he).hom ≫
        (fiberConeAugmented s F).hom =
      singularLiftProjection p (supportedNerve s).toSSet χ ≫
        TopCat.toSSet.map (TopCat.ofHom (coveringProductRetraction e)) ≫
          (discreteSingularIso F).hom := rfl

include hv hmin he in
set_option backward.isDefEq.respectTransparency false in
/-- For a cone and a genuine product covering, the actual
characteristic projection is a quasi-isomorphism as soon as the actual
fiber retraction is. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem singularLiftConeComparison_quasiIso
    (hret : QuasiIso (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom (coveringProductRetraction e)))
        integralCoefficient.{u})) :
    QuasiIso (SSet.chainComplexMap
      (singularLiftProjection p (supportedNerve s).toSSet χ) integralCoefficient.{u}) := by
  let T := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integralCoefficient
  let iso := singularLiftTrivializationIso p (supportedNerve s).toSSet χ e he
  let := hret
  let : QuasiIso (T.map (fiberConeAugmented s F).hom) :=
    SSet.chainComplexMap_quasiIso_of_extraDegeneracy (fiberConeAugmented s F)
      (fiberConeExtraDegeneracy s v hv hmin F) integralCoefficient
  have hwhole : QuasiIso (T.map (iso.hom ≫ (fiberConeAugmented s F).hom)) := by
    rw [Functor.map_comp]
    infer_instance
  have hcomm := singularLiftCone_augmentation s p χ e he
  change QuasiIso (T.map ((singularLiftTrivializationIso p
    (supportedNerve s).toSSet χ e he).hom ≫ (fiberConeAugmented s F).hom)) at hwhole
  rw [hcomm, Functor.map_comp, Functor.map_comp] at hwhole
  exact (quasiIso_iff_comp_right _ _).mp hwhole

end PoincareMT.Proofs.M59
