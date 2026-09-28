import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.IntegralCompactCohomology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralSupportUniv
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex TopologicalSpace Set

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralHomology_empty_isZero (q : Nat) :
    IsZero (integralHomology (∅ : Set X) q) := by
  have hchain (n : Nat) (a : (integralChains (∅ : Set X)).X n) : a = 0 := by
    apply (integralChainCoordinates (∅ : Set X) n).injective
    ext s
    exact (s ⟨Pi.single (0 : Fin (n + 1)) 1, single_mem_stdSimplex Real 0⟩).property.elim
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_isZero_X₂ _
    (ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b =>
      (hchain q a).trans (hchain q b).symm⟩)

theorem integralCohomology_empty_isZero (q : Nat) :
    IsZero (integralCohomology (∅ : Set (EuclideanSpace Real (Fin 3))) q) := by
  let X := (∅ : Set (EuclideanSpace Real (Fin 3)))
  have hchain (n : Nat) (a : (integralChains X).X n) : a = 0 := by
    apply (integralChainCoordinates X n).injective
    ext s
    exact (s ⟨Pi.single (0 : Fin (n + 1)) 1, single_mem_stdSimplex Real 0⟩).property.elim
  let : Subsingleton ((integralChains X).X q) :=
    ⟨fun a b => (hchain q a).trans (hchain q b).symm⟩
  let : Subsingleton ((integralCochains X).X q) := ⟨by
    intro phi psi
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    rw [hchain q a, map_zero, map_zero]⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_isZero_X₂ _
    (ModuleCat.isZero_of_subsingleton ((integralCochains X).X q))

theorem integralCompactSupportCohomology_empty_isZero (q : Nat) :
    IsZero (integralCompactSupportCohomology (∅ : Set (EuclideanSpace Real (Fin 3))) q) := by
  let X := (∅ : Set (EuclideanSpace Real (Fin 3)))
  let : CompactSpace X := ⟨by simp⟩
  exact (integralCohomology_empty_isZero q).of_iso
    (integralCompactSupportCohomologyIso q)

end Poincare.Topology
