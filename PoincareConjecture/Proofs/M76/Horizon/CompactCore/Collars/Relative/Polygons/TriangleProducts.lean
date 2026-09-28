import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Products.FaceProduct

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

local notation "I" => Icc (-1 : ℝ) 1

theorem SurfaceTriangleFibers.exists_triangle_product
    {T : CoorientedSurfaceStars E} (F : SurfaceTriangleFibers T)
    {s : Finset E} (hs : s ∈ (T.marked 2).faces)
    (hcard : s.card = 3) :
    ∃ P : SurfaceFaceProduct T s, ∀ x, P.map x = F.map s x.2 := by
  classical
  let B := T.dualRegion s ∩ (T.marked 2).space
  have hbase : B = {s.centroid ℝ id} := T.triangle_base_eq_singleton hs hcard
  have hF := F.piecewiseAffine s hs hcard
  obtain ⟨K, hK, hKs, _⟩ := hF
  let a : ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.const ℝ ℝ (s.centroid ℝ id)).prod (ContinuousAffineMap.id ℝ ℝ)
  have ha : InjOn a K.space := by
    intro x _ y _ h
    exact congrArg (fun z : E × ℝ => z.2) h
  let L := (K.affineOnFaces_affine a).embeddedImage ha
  have hL : L.faces.Finite := (K.affineOnFaces_affine a).embeddedImage_finite ha hK
  have hLs : L.space = B ×ˢ I := by
    rw [(K.affineOnFaces_affine a).embeddedImage_space ha, hKs, hbase]
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨rfl, hr⟩
    · rintro ⟨hx, hr⟩
      exact ⟨x.2, hr, Prod.ext hx.symm rfl⟩
  have hproj : FinitePiecewiseAffineOn (Prod.snd : E × ℝ → ℝ)
      (B ×ˢ I) :=
    ⟨L, hL, hLs, L.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap⟩
  let g : E × ℝ → E := fun x => F.map s x.2
  have hg : FinitePiecewiseAffineOn g (B ×ˢ I) :=
    (F.piecewiseAffine s hs hcard).comp hproj (fun _ hx => hx.2)
  have hi : InjOn g (B ×ˢ I) := by
    intro x hx y hy he
    apply Prod.ext
    · exact (hbase.subset hx.1).trans (hbase.subset hy.1).symm
    · exact F.injective s hs hcard hx.2 hy.2 he
  have him : g '' (B ×ˢ I) = T.dualRegion s := by
    rw [← F.image_eq s hs hcard]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(s.centroid ℝ id, r), ⟨hbase.symm.subset rfl, hr⟩, rfl⟩
  have hcentral : ∀ x ∈ B, g (x, 0) = x := by
    intro x hx
    exact (F.central s hs hcard).trans (hbase.subset hx).symm
  have hnotrim : s.centroid ℝ id ∉ T.dualRegionRim s := by
    intro hx
    have hr := (F.rim s hs hcard 0 (by norm_num)).mp
      ((F.central s hs hcard).symm ▸ hx)
    norm_num at hr
  have hboundary := T.triangle_dualRegion_inter_boundary hs hcard
  refine ⟨⟨g, hg, hi, him, hcentral, ?_, ?_, ?_, ?_⟩, fun _ => rfl⟩
  · intro x hx
    exact iff_of_false
      (fun h => hboundary.subset ⟨him.subset (mem_image_of_mem g hx), h⟩)
      (fun h => hboundary.subset ⟨hx.1.1, h⟩)
  · intro x hx
    have hn : x.1 ∉ T.dualRegionRim s ∩ (T.marked 2).space := by
      intro h
      exact hnotrim ((hbase.subset hx.1) ▸ h.1)
    simpa only [g, hn, false_or] using F.rim s hs hcard x.2 hx.2
  · intro p hp x hx
    exact F.positive s hs hcard p hp x.2 hx.2
  · intro p hp x hx
    exact F.negative s hs hcard p hp x.2 hx.2

end Geometry.SimplicialComplex
