import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ComponentHomotopySection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set CategoryTheory Limits
open scoped Topology
universe u v
namespace PoincareConjecture.M76.CutGraph

theorem module_homology_retract_of_homotopy_section
    {K : Type v} [Ring K] (A : ModuleCat.{u} K)
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (s : C(X,Y)) (r : C(Y,X)) (H : (r.comp s).Homotopic (ContinuousMap.id X))
    (n : ℕ)
    (i : A ⟶ (TopCat.toSSet.obj (TopCat.of X)).homology A n)
    (p : (TopCat.toSSet.obj (TopCat.of X)).homology A n ⟶ A)
    (hip : i ≫ p = 𝟙 A) :
    ∃ (j : A ⟶ (TopCat.toSSet.obj (TopCat.of Y)).homology A n)
      (q : (TopCat.toSSet.obj (TopCat.of Y)).homology A n ⟶ A), j ≫ q = 𝟙 A := by
  refine ⟨i ≫ moduleHomologyMap A s n,moduleHomologyMap A r n ≫ p,?_⟩
  have hh := moduleHomologyMap_section_comp A r s H n
  simp only [Category.assoc,← Category.assoc (moduleHomologyMap A s n),hh,Category.id_comp,hip]

theorem module_homology_retract_of_homotopyEquiv
    {K : Type v} [Ring K] (A : ModuleCat.{u} K)
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ)
    (i : A ⟶ (TopCat.toSSet.obj (TopCat.of X)).homology A n)
    (p : (TopCat.toSSet.obj (TopCat.of X)).homology A n ⟶ A)
    (hip : i ≫ p = 𝟙 A) :
    ∃ (j : A ⟶ (TopCat.toSSet.obj (TopCat.of Y)).homology A n)
      (q : (TopCat.toSSet.obj (TopCat.of Y)).homology A n ⟶ A), j ≫ q = 𝟙 A :=
  module_homology_retract_of_homotopy_section A e.toFun e.invFun e.left_inv n i p hip

end PoincareConjecture.M76.CutGraph
