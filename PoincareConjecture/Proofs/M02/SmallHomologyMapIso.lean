import PoincareConjecture.Proofs.M02.SmallHomologyMapMono
import PoincareConjecture.Proofs.M02.SmallHomologyMapEpi

set_option autoImplicit false

open CategoryTheory

universe u v

namespace PoincareConjecture.Proofs.M02

noncomputable section

variable {X : Type u} [TopologicalSpace X] {I : Type v}

theorem integral_small_inclusion_homologyMap_isIso_succ
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (n : Nat) :
    IsIso (HomologicalComplex.homologyMap
      (PoincareConjecture.Proofs.M02.Topology.integralSmallChainInclusion U) (n + 1)) := by
  let f := PoincareConjecture.Proofs.M02.Topology.integralSmallChainInclusion U
  have : Mono (HomologicalComplex.homologyMap f (n + 1)) := by
    exact integral_small_inclusion_homologyMap_mono_succ U hU hcover n
  have : Epi (HomologicalComplex.homologyMap f (n + 1)) := by
    exact integral_small_inclusion_homologyMap_epi_succ U hU hcover n
  exact isIso_of_mono_of_epi _

end

end PoincareConjecture.Proofs.M02
