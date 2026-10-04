import PoincareLib.AlgebraicTopology.SingularHomology.Chains.IntegralChainCoordinates
import PoincareLib.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralSupportMayerVietoris

/-!
# Absolute homology as homology supported on the whole space

The singular chains of the empty subspace vanish in every degree. Thus the
actual quotient projection for the pair with empty subspace is an isomorphism.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex Set

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSubspaceChains_empty : integralSubspaceChains (∅ : Set X) = 0 := by
  classical
  have hzero (n : Nat) (a : (integralChains (∅ : Set X)).X n) : a = 0 := by
    apply (integralChainCoordinates (∅ : Set X) n).injective
    ext s
    exact (s ⟨Pi.single (0 : Fin (n + 1)) 1, single_mem_stdSimplex Real 0⟩).property.elim
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rw [hzero n a]
  simp

theorem integralRelativeProjection_empty_isIso :
    IsIso (integralRelativeProjection (∅ : Set X)) := by
  change IsIso (cokernel.π (integralSubspaceChains (∅ : Set X)))
  rw [integralSubspaceChains_empty]
  infer_instance

def integralHomologySupportUnivIso (X : Type u) [TopologicalSpace X] (n : Nat) :
    integralHomology X n ≅ integralSupportHomology (univ : Set X) n := by
  let := integralRelativeProjection_empty_isIso (X := X)
  have : IsIso (integralToRelativeHomology (∅ : Set X) n) := by
    change IsIso ((homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) n).map
      (integralRelativeProjection (∅ : Set X)))
    infer_instance
  change integralHomology X n ≅ integralRelativeHomology (univ : Set X)ᶜ n
  rw [Set.compl_univ]
  exact asIso (integralToRelativeHomology (∅ : Set X) n)

end Poincare.Topology
