import PoincareConjecture.Proofs.M02.Topology.IntegralCompactCohomologyOpenMap

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open PoincareConjecture.Proofs.M02.Topology
open scoped unitInterval

universe u

namespace PoincareConjecture.Proofs.M53

theorem integralRelativeMap_homology_isIso_of_pair_inverse
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B A)
    (HX : ContinuousMap.Homotopy (g.comp f) (ContinuousMap.id X))
    (HY : ContinuousMap.Homotopy (f.comp g) (ContinuousMap.id Y))
    (hHX : ∀ t : unitInterval, Set.MapsTo (fun x => HX (t, x)) A A)
    (hHY : ∀ t : unitInterval, Set.MapsTo (fun y => HY (t, y)) B B) (n : Nat) :
    IsIso (homologyMap (integralRelativeMap f hf) n) := by
  have hid {Z : Type u} [TopologicalSpace Z] (D : Set Z) :
      integralRelativeMap (ContinuousMap.id Z) (A := D) (B := D)
        (fun _ hx => hx) = 𝟙 (integralRelativeChains D) := by
    apply (cancel_epi (integralRelativeProjection D)).mp
    exact (integralRelativeMap_projection _ _).trans (by
      change integralChainsFunctor.map (𝟙 (TopCat.of Z)) ≫ integralRelativeProjection D =
        integralRelativeProjection D ≫ 𝟙 _
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])
  obtain ⟨TX⟩ := integral_relative_homotopy HX (hg.comp hf) (fun _ hx => hx) hHX
  obtain ⟨TY⟩ := integral_relative_homotopy HY (hf.comp hg) (fun _ hy => hy) hHY
  let e : integralRelativeHomology A n ≅ integralRelativeHomology B n :=
    { hom := homologyMap (integralRelativeMap f hf) n
      inv := homologyMap (integralRelativeMap g hg) n
      hom_inv_id := by
        rw [← homologyMap_comp, integralRelativeMap_comp]
        exact (TX.homologyMap_eq n).trans (by rw [hid, homologyMap_id])
      inv_hom_id := by
        rw [← homologyMap_comp, integralRelativeMap_comp]
        exact (TY.homologyMap_eq n).trans (by rw [hid, homologyMap_id]) }
  exact e.isIso_hom

end PoincareConjecture.Proofs.M53
