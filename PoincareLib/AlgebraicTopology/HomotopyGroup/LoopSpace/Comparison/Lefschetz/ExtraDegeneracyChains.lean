import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Extra degeneracies give the actual augmented-chain comparison

The extra-degeneracy section and simplicial homotopy give a chain homotopy
equivalence from the original chains to chains of the constant augmentation
set. Its forward map is the actual simplicial augmentation.
Source: the cone argument in Hatcher, Theorem 2.27, pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v w

namespace SSet

variable {C : Type v} [Category.{w} C] [Preadditive C]
  [HasCoproducts.{u} C] [CategoryWithHomology C]

set_option backward.isDefEq.respectTransparency false in
/-- A simplicial augmentation with extra degeneracy induces a
quasi-isomorphism to the actual constant simplicial set of fiber labels.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem chainComplexMap_quasiIso_of_extraDegeneracy
    (A : SimplicialObject.Augmented (Type u))
    (ed : SimplicialObject.Augmented.ExtraDegeneracy A) (R : C) :
    QuasiIso (chainComplexMap A.hom R) := by
  let e : HomotopyEquiv (SSet.chainComplex A.left R)
      (SSet.chainComplex ((SimplicialObject.const (Type u)).obj A.right) R) := {
    hom := chainComplexMap A.hom R
    inv := chainComplexMap ed.section_ R
    homotopyHomInvId := by
      have h := (ed.homotopy.whiskerRight (sigmaConst.obj R)).toChainHomotopy
      change Homotopy (((chainComplexFunctor C).obj R).map (A.hom ≫ ed.section_))
        (((chainComplexFunctor C).obj R).map (𝟙 A.left)) at h
      have hi := ((chainComplexFunctor C).obj R).map_id (show SSet.{u} from A.left)
      rw [hi] at h
      simpa only [CategoryTheory.Functor.map_comp] using h
    homotopyInvHomId := by
      apply Homotopy.ofEq
      have h : ed.section_ ≫ A.hom = 𝟙 _ := by
        ext n : 1
        exact ed.section_app_comp_hom_app n
      change ((chainComplexFunctor C).obj R).map ed.section_ ≫
        ((chainComplexFunctor C).obj R).map A.hom = _
      rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id] }
  exact e.quasiIso_hom

end SSet
