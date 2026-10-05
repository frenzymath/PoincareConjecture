import PoincareLib.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.IntegralCompactCohomologyOpenMap

/-!
# Relative homology maps with a homotopy inverse of pairs

Specified homotopies preserving the relative subspaces make the actual
induced relative homology maps inverse. This is Hatcher, Proposition 2.19,
p. 118. It is used for the cylinder model in the sphere-separation repair
of Morgan--Tian, Proposition 15.12 and Remark 15.13, p. 365; see M53
derivation 06.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open Poincare.Topology
open scoped unitInterval

universe u

namespace PoincareMT.Topology.EmbeddedSphere

/-- Maps with a specified homotopy inverse through maps of pairs induce
isomorphisms on actual integral relative homology. The homotopies must
preserve the indicated subspaces at every time. Hatcher, Prop. 2.19, p. 118. -/
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

end PoincareMT.Topology.EmbeddedSphere
