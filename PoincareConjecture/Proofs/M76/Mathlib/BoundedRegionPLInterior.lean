import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexFacets
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem AffineOnFaces.mem_interior_image_of_convex_space
    {K : SimplicialComplex ℝ E} {f : E → F} (hf : K.AffineOnFaces f)
    (hK : K.faces.Finite) (hcv : Convex ℝ K.space)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hinj : InjOn f K.space) {x : E} (hx : x ∈ interior K.space) :
    f x ∈ interior (f '' K.space) := by
  classical
  let L := hf.embeddedImage hinj
  have hfaces : L.faces = (fun s : Finset E => s.image f) '' K.faces :=
    hf.embeddedImage_faces hinj
  have hspace : L.space = f '' K.space := hf.embeddedImage_space hinj
  have hcard : ∀ s ∈ K.faces, (s.image f).card = s.card := fun s hs =>
    Finset.card_image_of_injOn (hinj.mono (K.subset_space hs))
  have hfacesinj : InjOn (fun s : Finset E => s.image f) K.faces := by
    intro s hs t ht he
    apply Finset.coe_injective
    apply (hinj.image_eq_image_iff (K.subset_space hs) (K.subset_space ht)).mp
    simpa only [Finset.coe_image] using congrArg (fun r : Finset F => (r : Set F)) he
  have hpure : ∀ s ∈ L.faces, ∃ t ∈ L.faces,
      s ⊆ t ∧ t.card = Module.finrank ℝ F + 1 := by
    intro s hs
    rw [hfaces] at hs
    obtain ⟨v, hv, rfl⟩ := hs
    obtain ⟨w, hw, hvw, hwcard⟩ :=
      K.exists_full_coface_of_convex_space hK hcv ⟨x, hx⟩ hv
    refine ⟨w.image f, hfaces ▸ mem_image_of_mem _ hw,
      Finset.image_subset_image hvw, ?_⟩
    rw [hcard w hw, hwcard, hdim]
  have hxL : f x ∈ L.space := hspace ▸ mem_image_of_mem f (interior_subset hx)
  have hresult := L.mem_interior_space_of_paired_facets_at
    (hf.embeddedImage_finite hinj hK) hpure hxL
  rw [hspace] at hresult
  apply hresult
  intro s hs hscard hxs
  rw [hfaces] at hs
  obtain ⟨v, hv, rfl⟩ := hs
  have hvcard : v.card = Module.finrank ℝ E := by
    rw [hcard v hv, ← hdim] at hscard
    exact hscard
  have hxv : x ∈ convexHull ℝ (v : Set E) := by
    rw [Finset.coe_image, ← hf.image_convexHull hv] at hxs
    obtain ⟨y, hyv, hyx⟩ := hxs
    have he := hinj (K.convexHull_subset_space hv hyv) (interior_subset hx) hyx
    exact he ▸ hyv
  obtain ⟨t, ht, u, hu, hvt, hvu, htcard, hucard, htu⟩ :=
    K.hasTwoFullCofaces_of_hull_meets_interior hK hcv hv hvcard ⟨x, hxv, hx⟩
  refine ⟨t.image f, hfaces ▸ mem_image_of_mem _ ht,
    u.image f, hfaces ▸ mem_image_of_mem _ hu,
    Finset.image_subset_image hvt, Finset.image_subset_image hvu, ?_, ?_, ?_⟩
  · rw [hcard t ht, htcard, hdim]
  · rw [hcard u hu, hucard, hdim]
  · exact fun he => htu (hfacesinj ht hu he)

end Geometry.SimplicialComplex

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

theorem IsFinitePLBallPair.sdiff_subset_interior_of_finrank_eq
    {s b : Set X} (hs : IsFinitePLBallPair E s b)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ X) : s \ b ⊆ interior s := by
  obtain ⟨_, C, _, hcv, _, e, he, heb⟩ := hs
  obtain ⟨f, ⟨K, hK, hKC, hfK⟩, hfv⟩ := he.symm
  have hinj : InjOn f K.space := by
    intro x hx y hy hxy
    have h : e.symm ⟨x, hKC.subset hx⟩ = e.symm ⟨y, hKC.subset hy⟩ :=
      Subtype.ext ((hfv ⟨x, hKC.subset hx⟩).trans
        (hxy.trans (hfv ⟨y, hKC.subset hy⟩).symm))
    exact congrArg Subtype.val (e.symm.injective h)
  have himage : f '' K.space = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hfv ⟨y, hKC.subset hy⟩ ▸ (e.symm ⟨y, hKC.subset hy⟩).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, hKC.symm.subset (e ⟨x, hx⟩).property, ?_⟩
      rw [← hfv, e.symm_apply_apply]
  rintro x ⟨hxs, hxb⟩
  have hxC : (e ⟨x, hxs⟩ : E) ∈ interior C := by
    by_contra hnot
    exact hxb ((heb ⟨x, hxs⟩).mpr ⟨subset_closure (e ⟨x, hxs⟩).property, hnot⟩)
  have hcvK : Convex ℝ K.space := by rwa [hKC]
  have hxK : (e ⟨x, hxs⟩ : E) ∈ interior K.space := by rwa [hKC]
  have hfx : f (e ⟨x, hxs⟩) = x := (hfv _).symm.trans
    (congrArg Subtype.val (e.symm_apply_apply ⟨x, hxs⟩))
  have hout := hfK.mem_interior_image_of_convex_space hK hcvK hdim hinj hxK
  rw [himage, hfx] at hout
  exact hout

end Set
