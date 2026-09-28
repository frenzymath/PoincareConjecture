import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryCylinderPullback
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckSpatialMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

variable {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ}
  {K : Set ℝ} {U : Set C.carrier}

noncomputable def ordinaryChapter11CylinderOpenPartialHomeomorph
    (e : GeneralizedFlowCylinder (G) C origin scale K U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ K) (ht : origin + s / scale ∈ I.domain) :
    OpenPartialHomeomorph C.carrier M := by
  let f := R.product.sliceIdentification ⟨origin + s / scale, ht⟩
  let b : C.carrier → M := f.symm ∘ e.forward s hs
  have htarget : ∀ y ∈ b '' U, f y ∈ e.forward s hs '' U := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (f.apply_symm_apply _).symm⟩
  have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b U :=
    f.symm.contMDiff.comp_contMDiffOn (e.forward_smooth s hs)
  have hismooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.inverse s hs ∘ f) (b '' U) :=
    (e.inverse_smooth s hs).comp f.contMDiff.contMDiffOn htarget
  refine {
    toFun := b
    invFun := e.inverse s hs ∘ f
    source := U
    target := b '' U
    map_source' := fun x hx => mem_image_of_mem b hx
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := hU
    open_target := ?_
    continuousOn_toFun := hsmooth.continuousOn
    continuousOn_invFun := hismooth.continuousOn
  }
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [Function.comp_apply, b, f.apply_symm_apply, e.left_inverse s hs hx] using hx
  · intro x hx
    simpa only [Function.comp_apply, b, f.apply_symm_apply] using e.left_inverse s hs hx
  · intro y hy
    change f.symm (e.forward s hs (e.inverse s hs (f y))) = y
    rw [e.right_inverse s hs (htarget y hy), f.symm_apply_apply]
  · have hopen := f.symm.toHomeomorph.isOpenMap _ (e.isOpen_forward_image hU hU (Subset.refl U) hs)
    have himage : f.symm.toHomeomorph '' (e.forward s hs '' U) = b '' U := by
      rw [image_image]
      rfl
    rwa [himage] at hopen

theorem ordinaryChapter11CylinderOpenPartialHomeomorph_apply
    (e : GeneralizedFlowCylinder (G) C origin scale K U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ K) (ht : origin + s / scale ∈ I.domain) (x : C.carrier) :
    ordinaryChapter11CylinderOpenPartialHomeomorph R e hU s hs ht x =
      ordinaryChapter11CylinderSpatialMap R e s hs x :=
  ordinaryChapter11_inverse_projection R ⟨origin + s / scale, ht⟩ (e.forward s hs x)

theorem ordinaryChapter11CylinderOpenPartialHomeomorph_source
    (e : GeneralizedFlowCylinder (G) C origin scale K U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ K) (ht : origin + s / scale ∈ I.domain) :
    (ordinaryChapter11CylinderOpenPartialHomeomorph R e hU s hs ht).source = U := rfl

theorem ordinaryChapter11CylinderOpenPartialHomeomorph_smooth
    (e : GeneralizedFlowCylinder (G) C origin scale K U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ K) (ht : origin + s / scale ∈ I.domain) :
    let a := ordinaryChapter11CylinderOpenPartialHomeomorph R e hU s hs ht
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ a a.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ a.symm a.target := by
  let f := R.product.sliceIdentification ⟨origin + s / scale, ht⟩
  constructor
  · exact f.symm.contMDiff.comp_contMDiffOn (e.forward_smooth s hs)
  · apply (e.inverse_smooth s hs).comp f.contMDiff.contMDiffOn
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (f.apply_symm_apply _).symm⟩

end PoincareConjecture.M34
