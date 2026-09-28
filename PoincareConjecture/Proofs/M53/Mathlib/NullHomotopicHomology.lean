import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

set_option autoImplicit false

open CategoryTheory Limits AlgebraicTopology

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasCoproducts.{w} C] [CategoryWithHomology C]

namespace AlgebraicTopology

theorem singularHomology_map_const (R : C) {X Y : TopCat.{w}} (y : Y)
    (n : Nat) (hn : n ≠ 0) :
    ((singularHomologyFunctor C n).obj R).map
      (TopCat.ofHom (ContinuousMap.const X y)) = 0 := by
  let a : X ⟶ TopCat.of PUnit.{w + 1} :=
    TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let b : TopCat.of PUnit.{w + 1} ⟶ Y :=
    TopCat.ofHom (ContinuousMap.const PUnit y)
  have hfactor : TopCat.ofHom (ContinuousMap.const X y) = a ≫ b := rfl
  have hzero := isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    C n R (TopCat.of PUnit.{w + 1}) hn
  rw [hfactor, Functor.map_comp,
    hzero.eq_of_tgt (((singularHomologyFunctor C n).obj R).map a) 0, zero_comp]

end AlgebraicTopology

namespace TopCat.Homotopy

theorem singularHomologyMap_eq_zero_of_const
    {X Y : TopCat.{w}} {f : X ⟶ Y} {y : Y}
    (H : TopCat.Homotopy f (TopCat.ofHom (ContinuousMap.const X y)))
    (R : C) (n : Nat) (hn : n ≠ 0) :
    ((singularHomologyFunctor C n).obj R).map f = 0 := by
  change HomologicalComplex.homologyMap
    (((singularChainComplexFunctor C).obj R).map f) n = 0
  rw [H.congr_homologyMap_singularChainComplexFunctor R n]
  exact singularHomology_map_const R y n hn

end TopCat.Homotopy
