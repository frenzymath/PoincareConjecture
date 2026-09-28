import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalFrontier










set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X]




theorem interior_preimage_top_face {A D : Set X} (hAD : A ⊆ interior D) :
    interior ((Subtype.val : frontier (D ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹'
      (A ×ˢ {1})) =
      (Subtype.val : frontier (D ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹'
        (interior A ×ˢ {1}) := by
  apply Subset.antisymm
  · intro p hp
    have hps := interior_subset hp
    change (p : X × ℝ) ∈ A ×ˢ {(1 : ℝ)} at hps
    obtain ⟨v, hvA, hv, hpv⟩ := mem_interior.mp hp
    obtain ⟨O, hO, hOv⟩ := Topology.IsEmbedding.subtypeVal.isInducing.isOpen_iff.mp hv
    let f : X → X × ℝ := fun x => (x, 1)
    let T : Set X := f ⁻¹' O ∩ interior D
    have hf : Continuous f := continuous_id.prodMk continuous_const
    have hT : IsOpen T := (hO.preimage hf).inter isOpen_interior
    have hTA : T ⊆ A := by
      intro x hx
      let y : frontier (D ×ˢ Icc (-1 : ℝ) 1) :=
        ⟨(x, 1), prod_singleton_one_subset_frontier_cylinder
          (Subset.rfl : D ⊆ D) ⟨interior_subset hx.2, rfl⟩⟩
      have hyv : y ∈ v := hOv.subset hx.1
      exact (hvA hyv).1
    have hpO : (p : X × ℝ) ∈ O := hOv.symm.subset hpv
    have hfp : f (p : X × ℝ).1 = (p : X × ℝ) := Prod.ext rfl hps.2.symm
    exact ⟨interior_maximal hTA hT ⟨hfp.symm ▸ hpO, hAD hps.1⟩, hps.2⟩
  · exact interior_maximal
      (preimage_mono (prod_mono interior_subset Subset.rfl))
      (isOpen_preimage_top_face isOpen_interior (interior_subset.trans hAD))




theorem closure_sdiff_eq_closure_interior_sdiff {B s : Set X}
    (hB : closure (interior B) = B) (hs : IsClosed s) :
    closure (B \ s) = closure (interior B \ s) := by
  apply Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    intro x hx
    change x ∈ closure (interior B ∩ sᶜ)
    exact hs.isOpen_compl.closure_inter ⟨hB.symm ▸ hx.1, hx.2⟩
  · exact closure_mono (fun _ hx => ⟨interior_subset hx.1, hx.2⟩)




theorem closure_compl_sdiff_of_interior_closure_eq {u v : Set X}
    (hu : interior (closure u) = u) (hv : IsClosed v) :
    closure (uᶜ \ v) = (interior (closure u ∪ v))ᶜ := by
  have hreg : closure (interior uᶜ) = uᶜ := by
    rw [interior_compl, closure_compl, hu]
  rw [closure_sdiff_eq_closure_interior_sdiff hreg hv, interior_compl,
    sdiff_eq, ← compl_union, closure_compl]





theorem closure_cylinderExterior_sdiff_top_face {U V D : Set X}
    (hU : interior (closure U) = U)
    (hUD : closure U ⊆ interior D) (hVD : closure V ⊆ interior D) :
    closure ((frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) \
      closure V ×ˢ {1}) =
      frontier (D ×ˢ Icc (-1 : ℝ) 1) \
        interior (closure U ∪ closure V) ×ˢ {1} := by
  let S := frontier (D ×ˢ Icc (-1 : ℝ) 1)
  let a : S → X × ℝ := Subtype.val
  let u : Set S := a ⁻¹' (U ×ˢ {1})
  let v : Set S := a ⁻¹' (closure V ×ˢ {1})
  have hucl : closure u = a ⁻¹' (closure U ×ˢ {1}) :=
    closure_preimage_top_face ((subset_closure.trans hUD).trans interior_subset)
  have hu : interior (closure u) = u := by
    rw [hucl, interior_preimage_top_face hUD, hU]
  have hv : IsClosed v := (isClosed_closure.prod isClosed_singleton).preimage
    continuous_subtype_val
  have hUnion : closure u ∪ v = a ⁻¹' ((closure U ∪ closure V) ×ˢ {1}) := by
    rw [hucl, union_prod, preimage_union]
  have hcomp := closure_compl_sdiff_of_interior_closure_eq hu hv
  rw [hUnion, interior_preimage_top_face (union_subset hUD hVD)] at hcomp
  have hraw : a '' (uᶜ \ v) = (S \ U ×ˢ {1}) \ closure V ×ˢ {1} := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.property, hp.1⟩, hp.2⟩
    · rintro ⟨⟨hxS, hxU⟩, hxV⟩
      exact ⟨⟨x, hxS⟩, ⟨hxU, hxV⟩, rfl⟩
  calc
    closure ((S \ U ×ˢ {1}) \ closure V ×ˢ {1}) = closure (a '' (uᶜ \ v)) :=
      congrArg closure hraw.symm
    _ = a '' closure (uᶜ \ v) := isClosed_frontier.isClosedEmbedding_subtypeVal.closure_image_eq _
    _ = S \ interior (closure U ∪ closure V) ×ˢ {1} := by
      rw [hcomp]
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.property, hp⟩
      · rintro ⟨hxS, hx⟩
        exact ⟨⟨x, hxS⟩, hx, rfl⟩

end Set
