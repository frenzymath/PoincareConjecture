import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.FiniteComplexHomology
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.FiniteTerminalPair
import PoincareLib.Topology.Manifold.Smoothing.RelativeApproximation.General.InteriorSourceModel

/-!
# Finite singular homology from the original compact PL domain

The original domain charts construct a finite geometric pair. Transport
the finite mod-two homology of its literal carrier through the constructed
homeomorphism. No finite model or homology finiteness is supplied.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

set_option backward.isDefEq.respectTransparency false in
/-- Every original compact PL domain has finite mod-two singular homology
in every degree, including the empty domain. -/
theorem PLDomain.finite_modTwo_homology
    {X : Type u} {ι : Type v} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (n : ℕ) :
    Module.Finite (ZMod 2)
      (SSet.homology (C := ModuleCat.{u} (ZMod 2)) (TopCat.toSSet.obj (TopCat.of R))
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) n) := by
  classical
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨s, F, K, L, H, _, _, hK, _⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_domain_finite_pair
      e he.compatible he.cover hR he.halfspace
  let iso := TopCat.toSSet.mapIso
    (TopCat.isoOfHomeo (X := TopCat.of R) (Y := TopCat.of K.space) H)
  let chainIso := ((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))).mapIso iso
  let homIso := ((homologyFunctor (ModuleCat.{u} (ZMod 2)) (.down ℕ) n).mapIso chainIso)
  let : Module.Finite (ZMod 2)
      ((homologyFunctor (ModuleCat.{u} (ZMod 2)) (.down ℕ) n).obj
        ((TopCat.toSSet.obj (TopCat.of K.space)).chainComplex
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))))) := by
    exact FiniteComplexHomology.finite_modTwo_homology K hK n
  exact Module.Finite.equiv homIso.symm.toLinearEquiv

end PoincareMT.M76
