import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.FiniteComplexHomology
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTerminalPair
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorSourceModel









set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u v

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

set_option backward.isDefEq.respectTransparency false in


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

end PoincareConjecture.M76
