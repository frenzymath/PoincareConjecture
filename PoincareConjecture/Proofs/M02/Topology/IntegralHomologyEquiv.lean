import PoincareConjecture.Proofs.M02.Topology.IntegralRelativeChains

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped ContinuousMap

universe u

namespace PoincareConjecture.Proofs.M02.Topology

def integralHomologyIsoOfHomotopyEquiv
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₕ Y) (n : Nat) : integralHomology X n ≅ integralHomology Y n where
  hom := HomologicalComplex.homologyMap
    (integralChainsFunctor.map (TopCat.ofHom h.toFun)) n
  inv := HomologicalComplex.homologyMap
    (integralChainsFunctor.map (TopCat.ofHom h.invFun)) n
  hom_inv_id := by
    rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp]
    let H : TopCat.Homotopy (TopCat.ofHom h.toFun ≫ TopCat.ofHom h.invFun)
        (𝟙 (TopCat.of X)) := Classical.choice h.left_inv
    simpa only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] using
      H.congr_homologyMap_singularChainComplexFunctor integralCoefficient n
  inv_hom_id := by
    rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp]
    let H : TopCat.Homotopy (TopCat.ofHom h.invFun ≫ TopCat.ofHom h.toFun)
        (𝟙 (TopCat.of Y)) := Classical.choice h.right_inv
    simpa only [CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] using
      H.congr_homologyMap_singularChainComplexFunctor integralCoefficient n

end PoincareConjecture.Proofs.M02.Topology
