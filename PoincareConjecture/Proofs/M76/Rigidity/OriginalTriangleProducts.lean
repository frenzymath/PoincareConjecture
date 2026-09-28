import PoincareConjecture.Proofs.M76.Rigidity.OriginalTriangleFibers









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}




structure OriginalDiskFaceProduct (T : OriginalProperDiskTriangulation e R j)
    (s : Finset (T.index → ℝ × V3)) where
  map : (T.index → ℝ × V3) × ℝ → (T.index → ℝ × V3)
  piecewiseAffine : FinitePiecewiseAffineOn map
    ((T.dualRegion s ∩ (T.marked 2).space) ×ˢ I)
  injective : InjOn map ((T.dualRegion s ∩ (T.marked 2).space) ×ˢ I)
  image_eq : map '' ((T.dualRegion s ∩ (T.marked 2).space) ×ˢ I) = T.dualRegion s
  central : ∀ x ∈ T.dualRegion s ∩ (T.marked 2).space, map (x, 0) = x
  proper : ∀ x ∈ (T.dualRegion s ∩ (T.marked 2).space) ×ˢ I,
    map x ∈ (T.marked 1).space ↔ x.1 ∈ (T.marked 1).space
  rim : ∀ x ∈ (T.dualRegion s ∩ (T.marked 2).space) ×ˢ I,
    map x ∈ T.dualRegionRim s ↔ x.1 ∈ T.dualRegionRim s ∩ (T.marked 2).space ∨
      x.2 ∈ ({-1, 1} : Set ℝ)
  positive : ∀ p : (T.marked 2).vertices, (p : T.index → ℝ × V3) ∈ s →
    ∀ x ∈ (T.dualRegion s ∩ (T.marked 2).space) ×ˢ I,
      0 ≤ T.height p (map x) ↔ 0 ≤ x.2
  negative : ∀ p : (T.marked 2).vertices, (p : T.index → ℝ × V3) ∈ s →
    ∀ x ∈ (T.dualRegion s ∩ (T.marked 2).space) ×ˢ I,
      T.height p (map x) ≤ 0 ↔ x.2 ≤ 0




theorem OriginalTriangleFibers.exists_triangle_product
    {T : OriginalProperDiskTriangulation e R j} (F : OriginalTriangleFibers T)
    {s : Finset (T.index → ℝ × V3)} (hs : s ∈ (T.marked 2).faces)
    (hcard : s.card = 3) :
    ∃ P : OriginalDiskFaceProduct T s, ∀ x, P.map x = F.map s x.2 := by
  classical
  let B := T.dualRegion s ∩ (T.marked 2).space
  have hbase : B = {s.centroid ℝ id} := T.triangle_base_eq_singleton hs hcard
  have hF := F.piecewiseAffine s hs hcard
  obtain ⟨K, hK, hKs, _⟩ := hF
  let a : ℝ →ᴬ[ℝ] (T.index → ℝ × V3) × ℝ :=
    (ContinuousAffineMap.const ℝ ℝ (s.centroid ℝ id)).prod (ContinuousAffineMap.id ℝ ℝ)
  have ha : InjOn a K.space := by
    intro x _ y _ h
    exact congrArg (fun z : (T.index → ℝ × V3) × ℝ => z.2) h
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
  have hproj : FinitePiecewiseAffineOn (Prod.snd : (T.index → ℝ × V3) × ℝ → ℝ)
      (B ×ˢ I) :=
    ⟨L, hL, hLs, L.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ (T.index → ℝ × V3) ℝ).toContinuousAffineMap⟩
  let g : (T.index → ℝ × V3) × ℝ → (T.index → ℝ × V3) := fun x => F.map s x.2
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

end PoincareConjecture.M76
