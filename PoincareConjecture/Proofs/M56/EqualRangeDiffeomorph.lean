import PoincareConjecture.Proofs.M56.ComponentModels














set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

private theorem m56SelectedComponent_right_inverse
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    {y : A.carrier} (hy : y ∈ Set.range C.inclusion) :
    C.inclusion (C.inverse y) = y := by
  obtain ⟨x, rfl⟩ := hy
  exact congrArg C.inclusion (C.left_inverse x)



noncomputable def m56EqualRangeDiffeomorph
    {A B : GeneralizedSliceCarrier.{u}}
    (P : SurgerySelectedComponent A) (Q : SurgerySelectedComponent B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (hforward : ∀ x, d (P.inclusion x) ∈ Set.range Q.inclusion)
    (hbackward : ∀ y, d.symm (Q.inclusion y) ∈ Set.range P.inclusion) :
    Diffeomorph (𝓡 3) (𝓡 3) P.carrier.carrier Q.carrier.carrier ∞ := by
  let f : P.carrier.carrier → Q.carrier.carrier := fun x =>
    Q.inverse (d (P.inclusion x))
  let g : Q.carrier.carrier → P.carrier.carrier := fun y =>
    P.inverse (d.symm (Q.inclusion y))
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f := by
    rw [← contMDiffOn_univ]
    exact Q.inverse_smooth.comp
      (d.contMDiff.comp P.inclusion_smooth).contMDiffOn (fun x _ => hforward x)
  have hg : ContMDiff (𝓡 3) (𝓡 3) ∞ g := by
    rw [← contMDiffOn_univ]
    exact P.inverse_smooth.comp
      (d.symm.contMDiff.comp Q.inclusion_smooth).contMDiffOn
      (fun y _ => hbackward y)
  refine {
    contMDiff_toFun := hf
    contMDiff_invFun := hg
    toEquiv := {
      toFun := f
      invFun := g
      left_inv := ?_
      right_inv := ?_ } }
  · intro x
    change P.inverse (d.symm (Q.inclusion (Q.inverse (d (P.inclusion x))))) = x
    rw [m56SelectedComponent_right_inverse Q (hforward x)]
    simp only [d.symm_apply_apply]
    exact P.left_inverse x
  · intro y
    change Q.inverse (d (P.inclusion (P.inverse (d.symm (Q.inclusion y))))) = y
    rw [m56SelectedComponent_right_inverse P (hbackward y)]
    simp only [d.apply_symm_apply]
    exact Q.left_inverse y



theorem m56EqualRangeDiffeomorph_inclusion
    {A B : GeneralizedSliceCarrier.{u}}
    (P : SurgerySelectedComponent A) (Q : SurgerySelectedComponent B)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (hforward : ∀ x, d (P.inclusion x) ∈ Set.range Q.inclusion)
    (hbackward : ∀ y, d.symm (Q.inclusion y) ∈ Set.range P.inclusion)
    (x : P.carrier.carrier) :
    Q.inclusion (m56EqualRangeDiffeomorph P Q d hforward hbackward x) =
      d (P.inclusion x) :=
  m56SelectedComponent_right_inverse Q (hforward x)



theorem m56RegionComponentDiffeomorph_exists
    {A B : GeneralizedSliceCarrier.{u}} {V : Set B.carrier}
    (R : SurgeryRegionEquivalence A B univ V)
    (Q : SurgerySelectedComponent B) (hQ : Set.range Q.inclusion = V) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier Q.carrier.carrier ∞,
      ∀ x, Q.inclusion (e x) = R.map x := by
  have hforward (x : A.carrier) : R.map x ∈ range Q.inclusion := by
    rw [hQ]
    exact R.map_image.subset ⟨x, mem_univ _, rfl⟩
  have hQmem (y : Q.carrier.carrier) : Q.inclusion y ∈ V :=
    hQ ▸ mem_range_self y
  let f : A.carrier → Q.carrier.carrier := fun x => Q.inverse (R.map x)
  let g : Q.carrier.carrier → A.carrier := fun y => R.inverse (Q.inclusion y)
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f := by
    rw [← contMDiffOn_univ]
    exact Q.inverse_smooth.comp R.map_smooth (fun x _ => hforward x)
  have hg : ContMDiff (𝓡 3) (𝓡 3) ∞ g := by
    rw [← contMDiffOn_univ]
    exact R.inverse_smooth.comp Q.inclusion_smooth.contMDiffOn (fun y _ => hQmem y)
  let e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier Q.carrier.carrier ∞ := {
    contMDiff_toFun := hf
    contMDiff_invFun := hg
    toEquiv := {
      toFun := f
      invFun := g
      left_inv := fun x => by
        change R.inverse (Q.inclusion (Q.inverse (R.map x))) = x
        rw [m56SelectedComponent_right_inverse Q (hforward x)]
        exact R.left_inverse (mem_univ x)
      right_inv := fun y => by
        change Q.inverse (R.map (R.inverse (Q.inclusion y))) = y
        rw [R.right_inverse (hQmem y)]
        exact Q.left_inverse y } }
  exact ⟨e, fun x => m56SelectedComponent_right_inverse Q (hforward x)⟩

end PoincareConjecture
