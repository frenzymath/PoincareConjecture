import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.TwistedIntervalComponents



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set CategoryTheory Limits HomologicalComplex
open scoped Topology
universe u
namespace PoincareConjecture.M76.TwistedInvolutionInterval

def physicalComponentHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) (x : X) : connectedComponent x ≃ₜ connectedComponent (H x) :=
  H.subtype (fun y => by
    constructor
    · intro hy
      exact H.continuous.image_connectedComponent_subset x ⟨y,hy,rfl⟩
    · intro hy
      have hh := H.symm.continuous.image_connectedComponent_subset (H x) ⟨H y,hy,rfl⟩
      simpa only [H.symm_apply_apply] using hh)

variable {S U : Type u} [TopologicalSpace S] [TopologicalSpace U]
  [CompactSpace S] [T2Space S] [LocallyPathConnectedSpace S]
  (τ : S ≃ₜ S) (hτ : Function.Involutive τ)
  (W : Model τ hτ ≃ₜ U)

theorem physical_invariant_component_homology_retract
    (hfree : ∀ x, τ x ≠ x) (x : S) (hx : τ x ∈ connectedComponent x)
    (R : ModuleCat.{u} (ZMod 2)) :
    ∃ (i : R ⟶ (TopCat.toSSet.obj
        (TopCat.of (connectedComponent (W (boundaryMap τ hτ x))))).homology R 1)
      (r : (TopCat.toSSet.obj
        (TopCat.of (connectedComponent (W (boundaryMap τ hτ x))))).homology R 1 ⟶ R),
      i ≫ r = 𝟙 R := by
  let C := connectedComponent x
  let : ConnectedSpace C := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let : LocallyPathConnectedSpace C :=
    (isOpen_connectedComponent : IsOpen (connectedComponent x)).locallyPathConnectedSpace
  let : PathConnectedSpace C := PathConnectedSpace.of_locallyPathConnectedSpace
  let θ := componentInvolution τ hτ hx
  let hθ := componentInvolution_involutive τ hτ hx
  have hθfree : ∀ y, θ y ≠ y := fun y he => hfree y (congrArg Subtype.val he)
  obtain ⟨V,_⟩ := exists_invariant_component_homeomorph τ hτ x hx
  let H := V.trans (physicalComponentHomeomorph W (boundaryMap τ hτ x))
  let iso := TopCat.toSSet.mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (Model θ hθ))
      (Y := TopCat.of (connectedComponent (W (boundaryMap τ hτ x)))) H)
  let e := (homologyFunctor (ModuleCat.{u} (ZMod 2)) (.down ℕ) 1).mapIso
    (((SSet.chainComplexFunctor (ModuleCat.{u} (ZMod 2))).obj R).mapIso iso)
  obtain ⟨i,r,hir⟩ := exists_homology_retract θ hθ hθfree R
  refine ⟨i ≫ e.hom,e.inv ≫ r,?_⟩
  simp only [Category.assoc,Iso.hom_inv_id_assoc,hir]

theorem physical_invariant_component_h1_not_isZero
    (hfree : ∀ x, τ x ≠ x) (x : S) (hx : τ x ∈ connectedComponent x)
    (R : ModuleCat.{u} (ZMod 2)) [Nontrivial R] :
    ¬ IsZero ((TopCat.toSSet.obj
      (TopCat.of (connectedComponent (W (boundaryMap τ hτ x))))).homology R 1) := by
  obtain ⟨i,r,hir⟩ := physical_invariant_component_homology_retract τ hτ W hfree x hx R
  intro hz
  have hi : i = 0 := hz.eq_of_tgt i 0
  have hid : 𝟙 R = 0 := hir.symm.trans (by rw [hi,zero_comp])
  have : Subsingleton R := ModuleCat.isZero_iff_subsingleton.mp
    ((IsZero.iff_id_eq_zero R).mpr hid)
  exact false_of_nontrivial_of_subsingleton R

theorem exists_physical_exchanged_component_product
    (x : S) (hx : τ x ∉ connectedComponent x) :
    ∃ V : (connectedComponent x × unitInterval) ≃ₜ
        connectedComponent (W (boundaryMap τ hτ x)),
      ∀ z, (V z : U) = W (projection τ hτ (z.1.val,z.2)) := by
  obtain ⟨V,hV⟩ := exists_exchanged_component_homeomorph τ hτ x hx
  exact ⟨V.trans (physicalComponentHomeomorph W (boundaryMap τ hτ x)),
    fun z => congrArg W (hV z)⟩

end PoincareConjecture.M76.TwistedInvolutionInterval
