import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.TrivialLift
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.ConeSimplicial
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.ExtraDegeneracyChains
import PoincareConjecture.Proofs.M02.Topology.IntegralHomologyEquiv












set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open scoped Simplicial MonoidalCategory

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J]
  (s : Finset J) (v : J) (hv : v ∈ s) (hmin : ∀ j ∈ s, v ≤ j)
  {E X F : Type u} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace F] [DiscreteTopology F]
  (p : C(E, X))
  (χ : (supportedNerve s).toSSet ⟶ TopCat.toSSet.obj (TopCat.of X))
  (e : E ≃ₜ X × F) (he : ∀ z, p z = (e z).1)



def coveringProductRetraction : C(E, F) :=
  ⟨fun z => (e z).2, continuous_snd.comp e.continuous⟩



theorem singularLiftCone_augmentation :
    (singularLiftTrivializationIso p (supportedNerve s).toSSet χ e he).hom ≫
        (fiberConeAugmented s F).hom =
      singularLiftProjection p (supportedNerve s).toSSet χ ≫
        TopCat.toSSet.map (TopCat.ofHom (coveringProductRetraction e)) ≫
          (discreteSingularIso F).hom := rfl

include hv hmin he in
set_option backward.isDefEq.respectTransparency false in



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

end PoincareConjecture.Proofs.M59
