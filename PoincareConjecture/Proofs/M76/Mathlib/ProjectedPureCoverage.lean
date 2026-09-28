import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedLinearImage
import PoincareConjecture.Proofs.M76.Mathlib.FinitePureCoverage

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem mem_interior_linearImage_of_paired_facets_at (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) (Q : E →L[ℝ] F) (hinj : InjOn Q K.space)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces,
      s ⊆ t ∧ t.card = Module.finrank ℝ F + 1)
    {x : E} (hx : x ∈ K.space)
    (hpair : ∀ s ∈ K.faces, s.card = Module.finrank ℝ F →
      x ∈ convexHull ℝ (s : Set E) → K.HasTwoFullCofaces (Module.finrank ℝ F) s) :
    Q x ∈ interior (Q '' K.space) := by
  classical
  let L := K.embeddedLinearImage Q hinj
  have hfaces : L.faces = (fun s : Finset E => s.image Q) '' K.faces :=
    K.embeddedLinearImage_faces Q hinj
  have hspace : L.space = Q '' K.space := K.embeddedLinearImage_space Q hinj
  have hcard : ∀ s ∈ K.faces, (s.image Q).card = s.card := fun s hs =>
    Finset.card_image_of_injOn (hinj.mono (K.subset_space hs))
  have hfacesinj : InjOn (fun s : Finset E => s.image Q) K.faces := by
    intro s hs t ht he
    apply Finset.coe_injective
    apply (hinj.image_eq_image_iff (K.subset_space hs) (K.subset_space ht)).mp
    simpa only [Finset.coe_image] using congrArg (fun r : Finset F => (r : Set F)) he
  have hLfinite : L.faces.Finite := by
    rw [hfaces]
    exact hfinite.image _
  have hLpure : ∀ s ∈ L.faces, ∃ t ∈ L.faces,
      s ⊆ t ∧ t.card = Module.finrank ℝ F + 1 := by
    intro s hs
    rw [hfaces] at hs
    obtain ⟨v, hv, rfl⟩ := hs
    obtain ⟨w, hw, hvw, hwcard⟩ := hpure v hv
    refine ⟨w.image Q, hfaces ▸ mem_image_of_mem _ hw, Finset.image_subset_image hvw, ?_⟩
    rw [hcard w hw]
    exact hwcard
  have hxL : Q x ∈ L.space := hspace ▸ mem_image_of_mem Q hx
  have hresult := L.mem_interior_space_of_paired_facets_at hLfinite hLpure hxL
  rw [hspace] at hresult
  apply hresult
  intro s hs hsCard hxs
  rw [hfaces] at hs
  obtain ⟨v, hv, rfl⟩ := hs
  have hvcard : v.card = Module.finrank ℝ F := by
    rwa [hcard v hv] at hsCard
  have hxv : x ∈ convexHull ℝ (v : Set E) := by
    rw [Finset.coe_image] at hxs
    have himage : Q '' convexHull ℝ (v : Set E) = convexHull ℝ (Q '' (v : Set E)) := by
      simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe] using
        Q.toLinearMap.toAffineMap.image_convexHull (v : Set E)
    rw [← himage] at hxs
    obtain ⟨y, hyv, hyx⟩ := hxs
    have he := hinj (K.convexHull_subset_space hv hyv) hx hyx
    exact he ▸ hyv
  obtain ⟨t, ht, u, hu, hvt, hvu, htcard, hucard, htu⟩ := hpair v hv hvcard hxv
  refine ⟨t.image Q, hfaces ▸ mem_image_of_mem _ ht,
    u.image Q, hfaces ▸ mem_image_of_mem _ hu,
    Finset.image_subset_image hvt, Finset.image_subset_image hvu, ?_, ?_, ?_⟩
  · rw [hcard t ht]
    exact htcard
  · rw [hcard u hu]
    exact hucard
  · exact fun he => htu (hfacesinj ht hu he)

end Geometry.SimplicialComplex
