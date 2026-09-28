import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Equiv

set_option autoImplicit false

open CategoryTheory Limits

universe w v u

namespace PoincareConjecture.Proofs.M02

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]
  [CategoryWithHomology C]

noncomputable section

variable {X Y : TopCat.{w}}

theorem singularHomologyMap_isIso_of_homotopyEquiv
    (R : C) (n : ℕ) (e : ContinuousMap.HomotopyEquiv X Y) :
    IsIso (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom e.toFun)) R n) := by
  let f : TopCat.{w} := X
  let g : TopCat.{w} := Y
  let F : f ⟶ g := TopCat.ofHom e.toFun
  let G : g ⟶ f := TopCat.ofHom e.invFun
  have hleft : TopCat.Homotopy (F ≫ G) (𝟙 f) := by
    exact Classical.choice e.left_inv
  have hright : TopCat.Homotopy (G ≫ F) (𝟙 g) := by
    exact Classical.choice e.right_inv
  have hleft' := SSet.Homotopy.congr_homologyMap hleft.toSSet R n
  have hright' := SSet.Homotopy.congr_homologyMap hright.toSSet R n
  apply IsIso.mk
  refine ⟨SSet.homologyMap (TopCat.toSSet.map G) R n, ?_, ?_⟩
  · change SSet.homologyMap (TopCat.toSSet.map F) R n ≫
      SSet.homologyMap (TopCat.toSSet.map G) R n = 𝟙 _
    rw [← SSet.homologyMap_comp, ← TopCat.toSSet.map_comp]
    convert hleft' using 1
    simp
  · change SSet.homologyMap (TopCat.toSSet.map G) R n ≫
      SSet.homologyMap (TopCat.toSSet.map F) R n = 𝟙 _
    rw [← SSet.homologyMap_comp, ← TopCat.toSSet.map_comp]
    convert hright' using 1
    simp

noncomputable def singularHomologyIso_of_homotopyEquiv
    (R : C) (n : ℕ) (e : ContinuousMap.HomotopyEquiv X Y) :
    (TopCat.toSSet.obj X).homology R n ≅ (TopCat.toSSet.obj Y).homology R n :=
  @asIso _ _ _ _ (SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom e.toFun)) R n)
    (singularHomologyMap_isIso_of_homotopyEquiv R n e)

@[simp]
theorem singularHomologyIso_of_homotopyEquiv_hom
    (R : C) (n : ℕ) (e : ContinuousMap.HomotopyEquiv X Y) :
    (singularHomologyIso_of_homotopyEquiv R n e).hom =
      SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom e.toFun)) R n := by
  rfl

end

end PoincareConjecture.Proofs.M02
