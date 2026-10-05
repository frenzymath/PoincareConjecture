import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.RawCutComponentHomotopy
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.ComponentHomologyTransport
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismTrimComponentTransport

/-! # Homology classes transported into literal old cut components -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set CategoryTheory Limits
open scoped Topology
universe u v
namespace PoincareMT.M76

theorem exists_raw_cut_component_homology_retract
    {E : Type u} [TopologicalSpace E]
    {U V Q : Set E} (R : ModuleCat.{u} (ZMod 2)) (T : U ≃ₜ V) (x : U)
    (i₀ : R ⟶ (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn U (x : E)))).homology R 1)
    (r₀ : (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn U (x : E)))).homology R 1 ⟶ R)
    (hi₀ : i₀ ≫ r₀ = 𝟙 R) (q : Q)
    (e : ContinuousMap.HomotopyEquiv
      (connectedComponentIn V (T x : E)) (connectedComponentIn Q q))
    (he : ∀ y, (e.invFun y : E) = y) :
    ∃ (i : R ⟶ (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn Q q))).homology R 1)
      (r : (TopCat.toSSet.obj (TopCat.of
        (connectedComponentIn Q q))).homology R 1 ⟶ R),
      i ≫ r = 𝟙 R := by
  let cT := PrismBelt.carrierComponentHomeomorph T x
  obtain ⟨i₁,r₁,hi₁⟩ := CutGraph.module_homology_retract_of_homotopyEquiv
    R cT.toHomotopyEquiv 1 i₀ r₀ hi₀
  obtain ⟨i₂,r₂,hi₂⟩ := CutGraph.module_homology_retract_of_homotopyEquiv
    R e 1 i₁ r₁ hi₁
  exact ⟨i₂,r₂,hi₂⟩

end PoincareMT.M76
