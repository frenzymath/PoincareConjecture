import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.NeighborhoodEulerLifts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.RegularClosedAttachment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.EndRim



set_option autoImplicit false
open Set Geometry Topology Metric

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks

variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem model_carrier_eq_of_preimage
    (K : SimplicialComplex ℝ E) {S : Set X} (H : K.space ≃ₜ S)
    (a : E → X) (haval : ∀ x : K.space, a x = (H x : X))
    {T : Set E} (hTK : T ⊆ K.space) {B : Set X}
    (hT : (Subtype.val : K.space → E) ⁻¹' T =
      H ⁻¹' ((Subtype.val : S → X) ⁻¹' B)) :
    T = K.space ∩ a ⁻¹' B := by
  ext x
  constructor
  · intro hx
    refine ⟨hTK hx,?_⟩
    have h := hT.subset (show (⟨x,hTK hx⟩ : K.space) ∈ Subtype.val ⁻¹' T from hx)
    change (H ⟨x,hTK hx⟩ : X) ∈ B at h
    rwa [← haval] at h
  · rintro ⟨hxK,hxB⟩
    have h : (⟨x,hxK⟩ : K.space) ∈ H ⁻¹' ((Subtype.val : S → X) ⁻¹' B) := by
      change (H ⟨x,hxK⟩ : X) ∈ B
      rwa [← haval]
    exact hT.symm.subset h

theorem closedComplement_original_carriers
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    {S Q A : Set X} (H : K.space ≃ₜ S) (a : E → X)
    (haval : ∀ x : K.space, a x = (H x : X)) (O : Set S)
    (hN : N.space = K.space ∩ a ⁻¹' Q)
    (hclosure : closure O = (Subtype.val : S → X) ⁻¹' Q)
    (hinterior : interior (closure O) = O)
    (hfrontier : frontier (closure O) = (Subtype.val : S → X) ⁻¹' A) :
    (K.closedFaceComplement N).space =
        K.space ∩ a ⁻¹' ((Subtype.val : S → X) '' Oᶜ) ∧
      (N ⊓ K.closedFaceComplement N).space = K.space ∩ a ⁻¹' A := by
  have hpreN : (Subtype.val : K.space → E) ⁻¹' N.space = H ⁻¹' closure O := by
    rw [hclosure]
    ext x
    simp only [mem_preimage,hN,mem_inter_iff,x.property,true_and,haval]
  constructor
  · apply model_carrier_eq_of_preimage K H a haval
      (SimplicialComplex.space_subset_of_le (K.closedFaceComplement_le N))
    rw [K.preimage_closedFaceComplement_space_eq_closure_compl N hK hNK,hpreN,
      ← preimage_compl,← H.preimage_closure,closure_compl,hinterior]
    congr 1
    exact (preimage_image_eq _ Subtype.val_injective).symm
  · rw [K.inter_closedFaceComplement_space_eq_relative_frontier N hK hNK,
      hpreN,← H.preimage_frontier,hfrontier]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,by simpa only [mem_preimage,haval] using hy⟩
    · rintro ⟨hxK,hxA⟩
      refine ⟨⟨x,hxK⟩,?_,rfl⟩
      change (H ⟨x,hxK⟩ : X) ∈ A
      rwa [← haval]

omit [FiniteDimensional ℝ E] in
theorem original_model_carrier_image
    (K : SimplicialComplex ℝ E) {S A : Set X} (H : K.space ≃ₜ S)
    (a : E → X) (haval : ∀ x : K.space, a x = (H x : X)) (hAS : A ⊆ S) :
    a '' (K.space ∩ a ⁻¹' A) = A := by
  apply Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact hx.2
  · intro y hy
    let z : S := ⟨y,hAS hy⟩
    have hval : a (H.symm z) = y := by rw [haval,H.apply_symm_apply]
    exact ⟨H.symm z,⟨(H.symm z).property,by change a (H.symm z) ∈ A; rwa [hval]⟩,hval⟩

omit [FiniteDimensional ℝ E] in
theorem isConnected_original_model_carrier
    (K : SimplicialComplex ℝ E) {S : Set X} (H : K.space ≃ₜ S)
    (a : E → X) (haval : ∀ x : K.space, a x = (H x : X))
    {B : Set S} (hB : IsConnected B) :
    IsConnected (K.space ∩ a ⁻¹' ((Subtype.val : S → X) '' B)) := by
  let q : S → E := fun z => (H.symm z : E)
  have hq : Continuous q := continuous_subtype_val.comp H.symm.continuous
  have himage : q '' B = K.space ∩ a ⁻¹' ((Subtype.val : S → X) '' B) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨(H.symm z).property,⟨z,hz,?_⟩⟩
      change (z : X) = a (H.symm z)
      rw [haval,H.apply_symm_apply]
    · rintro ⟨hyK,z,hz,hzy⟩
      have heq : H ⟨y,hyK⟩ = z :=
        Subtype.ext ((haval ⟨y,hyK⟩).symm.trans hzy.symm)
      refine ⟨z,hz,?_⟩
      change (H.symm z : E) = y
      rw [← heq,H.symm_apply_apply]
  exact himage ▸ hB.image q hq.continuousOn

theorem exists_original_finitePL_rim_model
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {e : ι → OpenPartialHomeomorph X V}
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K T : SimplicialComplex ℝ E) {S A : Set X} (H : K.space ≃ₜ S)
    (a : E → X) (ha : PolyhedralPLInCharts e a K.space)
    (haval : ∀ x : K.space, a x = (H x : X))
    (hT : T.space = K.space ∩ a ⁻¹' A)
    (c : (Fin 2 → ℝ) → X) (hc : PolyhedralPLInCharts e c (sphere 0 1))
    (hci : InjOn c (sphere 0 1)) (hcS : MapsTo c (sphere 0 1) S)
    (hcA : c '' sphere 0 1 = A) :
    ∃ γ : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ T.space,
      γ.IsFinitePL ∧ ∀ z, a (γ z) = c z := by
  obtain ⟨J,hJ,hJs⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  obtain ⟨g,hg,hgi,hgK,hgv⟩ := exists_finitePL_lift_of_original_embedding hcompat
    K H a ha haval J hJ c (hJs.symm ▸ hc) (hJs.symm ▸ hci) (hJs.symm ▸ hcS)
  have hg' : FinitePiecewiseAffineOn g (sphere (0 : Fin 2 → ℝ) 1) := hJs ▸ hg
  have hgi' : InjOn g (sphere (0 : Fin 2 → ℝ) 1) := hJs ▸ hgi
  have hai : InjOn a K.space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((haval ⟨x,hx⟩).symm.trans (hxy.trans (haval ⟨y,hy⟩)))))
  have himage : g '' sphere (0 : Fin 2 → ℝ) 1 = T.space := by
    rw [hT,← hcA]
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨hgK (hJs.symm.subset hz),⟨z,hz,(hgv z (hJs.symm.subset hz)).symm⟩⟩
    · rintro ⟨hyK,z,hz,hzy⟩
      exact ⟨z,hz,hai (hgK (hJs.symm.subset hz)) hyK
        ((hgv z (hJs.symm.subset hz)).trans hzy)⟩
  obtain ⟨G,hG,hGval⟩ := hg'.exists_homeomorph_image hgi'
  let γ := G.trans (Homeomorph.setCongr himage)
  refine ⟨γ,?_,?_⟩
  · exact ⟨g,hg',fun z => hGval z⟩
  · intro z
    change a (G z) = c z
    rw [hGval]
    exact hgv z (hJs.symm.subset z.property)

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
