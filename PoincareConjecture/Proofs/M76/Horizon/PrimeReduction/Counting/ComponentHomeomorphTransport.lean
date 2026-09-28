import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.PhysicalIntervalComponentHomology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ComponentHomologyTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointComponentAlternatives



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set CategoryTheory Limits HomologicalComplex
open scoped Topology
universe u v

namespace PoincareConjecture.M76

theorem module_homology_retract_of_component_homeomorph
    {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    {U : Set E} {V : Set F} (h : U ≃ₜ V) (x : U)
    {R : ModuleCat.{u} (ZMod 2)}
    (i : R ⟶ (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn U (x : E)))).homology R 1)
    (r : (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn U (x : E)))).homology R 1 ⟶ R)
    (hir : i ≫ r = 𝟙 R) :
    ∃ (j : R ⟶ (TopCat.toSSet.obj (TopCat.of
        (connectedComponentIn V (h x : F)))).homology R 1)
      (s : (TopCat.toSSet.obj (TopCat.of
        (connectedComponentIn V (h x : F)))).homology R 1 ⟶ R),
      j ≫ s = 𝟙 R := by
  let c₀ := PrismBelt.subtypeConnectedComponentHomeomorph x
  let c₁ := PrismBelt.subtypeConnectedComponentHomeomorph (h x)
  let c₂ := TwistedInvolutionInterval.physicalComponentHomeomorph h x
  let c : connectedComponentIn U (x : E) ≃ₜ
      connectedComponentIn V (h x : F) := c₀.symm.trans (c₂.trans c₁)
  let iso := TopCat.toSSet.mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (connectedComponentIn U (x : E)))
      (Y := TopCat.of (connectedComponentIn V (h x : F))) c)
  let e := (homologyFunctor (ModuleCat.{u} (ZMod 2)) (.down ℕ) 1).mapIso
    (((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj R).mapIso iso)
  refine ⟨i ≫ e.hom, e.inv ≫ r, ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc, hir]

end PoincareConjecture.M76
