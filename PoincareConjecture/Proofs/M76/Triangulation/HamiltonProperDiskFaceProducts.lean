import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskFacetFibers

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : Cube ≃ₜ D}
  {T : HamiltonProperDiskTriangulation R D b} {c : E ≃ᴬ[ℝ] V}

structure HamiltonProperDiskTriangleFibers
    (C : HamiltonProperDiskCoherentSides T c) where
  map : Finset E → ℝ → E
  piecewiseAffine : ∀ s ∈ T.disk.faces, s.card = 3 → FinitePiecewiseAffineOn (map s) I
  injective : ∀ s ∈ T.disk.faces, s.card = 3 → InjOn (map s) I
  image_eq : ∀ s ∈ T.disk.faces, s.card = 3 → map s '' I = T.dualRegion s
  central : ∀ s ∈ T.disk.faces, s.card = 3 → map s 0 = s.centroid ℝ id
  rim : ∀ s ∈ T.disk.faces, s.card = 3 → ∀ t ∈ I,
    map s t ∈ T.dualRegionRim s ↔ t ∈ ({-1, 1} : Set ℝ)
  positive : ∀ s ∈ T.disk.faces, s.card = 3 →
    ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ t ∈ I,
      0 ≤ C.labels.height p (map s t) ↔ 0 ≤ t
  negative : ∀ s ∈ T.disk.faces, s.card = 3 →
    ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ t ∈ I,
      C.labels.height p (map s t) ≤ 0 ↔ t ≤ 0

structure HamiltonProperDiskFaceProduct
    (C : HamiltonProperDiskCoherentSides T c) (s : Finset E) where
  map : E × ℝ → E
  piecewiseAffine : FinitePiecewiseAffineOn map (T.diskDualBase s ×ˢ I)
  injective : InjOn map (T.diskDualBase s ×ˢ I)
  image_eq : map '' (T.diskDualBase s ×ˢ I) = T.dualRegion s
  central : ∀ x ∈ T.diskDualBase s, map (x, 0) = x
  proper : ∀ x ∈ T.diskDualBase s ×ˢ I, map x ∈ frontier R ↔ x.1 ∈ frontier R
  rim : ∀ x ∈ T.diskDualBase s ×ˢ I,
    map x ∈ T.dualRegionRim s ↔ x.1 ∈ T.dualRegionRim s ∩ D ∨
      x.2 ∈ ({-1, 1} : Set ℝ)
  positive : ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ x ∈ T.diskDualBase s ×ˢ I,
    0 ≤ C.labels.height p (map x) ↔ 0 ≤ x.2
  negative : ∀ p : T.disk.vertices, (p : E) ∈ s → ∀ x ∈ T.diskDualBase s ×ˢ I,
    C.labels.height p (map x) ≤ 0 ↔ x.2 ≤ 0

variable [FiniteDimensional ℝ E]

theorem HamiltonProperDiskCoherentSides.exists_triangle_fibers
    (C : HamiltonProperDiskCoherentSides T c) (h3 : Module.finrank ℝ E = 3)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1) :
    Nonempty (HamiltonProperDiskTriangleFibers C) := by
  classical
  let S := {s : Finset E // s ∈ T.disk.faces ∧ s.card = 3}
  choose F hF hi him h0 hrim hpos hneg using
    fun s : S => C.exists_triangle_fiber h3 hproper s.property.1 s.property.2
  let f : Finset E → ℝ → E := fun s =>
    if h : s ∈ T.disk.faces ∧ s.card = 3 then F ⟨s, h⟩ else fun _ => 0
  have hval (s : S) : f s = F s := by
    simp only [f, dif_pos s.property]
    rfl
  refine ⟨⟨f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hF ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hi ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact him ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact h0 ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hrim ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hpos ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hneg ⟨s, hs, hc⟩

theorem HamiltonProperDiskTriangleFibers.exists_triangle_product
    {C : HamiltonProperDiskCoherentSides T c} (F : HamiltonProperDiskTriangleFibers C)
    (hproper : ∀ x : Cube, (b x : E) ∈ frontier R ↔ (x : V2) ∈ sphere 0 1)
    {s : Finset E} (hs : s ∈ T.disk.faces) (hcard : s.card = 3) :
    ∃ P : HamiltonProperDiskFaceProduct C s, ∀ x, P.map x = F.map s x.2 := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have hbase := T.triangle_base_eq_singleton hs hcard
  have hinside : T.dualRegion s ⊆ interior R :=
    inter_subset_left.trans
      (T.dualBlock_subset_interior hs (T.disk_triangle_not_boundary hproper hs hcard))
  have hF := F.piecewiseAffine s hs hcard
  obtain ⟨K, hK, hKs, _⟩ := hF
  let j : ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.const ℝ ℝ (s.centroid ℝ id)).prod (ContinuousAffineMap.id ℝ ℝ)
  have hj : InjOn j K.space := by
    intro x _ y _ h
    exact congrArg (fun z : E × ℝ => z.2) h
  let L := (K.affineOnFaces_affine j).embeddedImage hj
  have hL : L.faces.Finite := (K.affineOnFaces_affine j).embeddedImage_finite hj hK
  have hLs : L.space = T.diskDualBase s ×ˢ I := by
    rw [(K.affineOnFaces_affine j).embeddedImage_space hj, hKs, hbase]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨rfl, ht⟩
    · rintro ⟨hx, ht⟩
      exact ⟨x.2, ht, Prod.ext hx.symm rfl⟩
  have hproj : FinitePiecewiseAffineOn (Prod.snd : E × ℝ → ℝ)
      (T.diskDualBase s ×ˢ I) :=
    ⟨L, hL, hLs, L.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap⟩
  let g : E × ℝ → E := fun x => F.map s x.2
  have hg : FinitePiecewiseAffineOn g (T.diskDualBase s ×ˢ I) :=
    (F.piecewiseAffine s hs hcard).comp hproj (fun _ hx => hx.2)
  have hi : InjOn g (T.diskDualBase s ×ˢ I) := by
    intro x hx y hy he
    apply Prod.ext
    · exact (hbase.subset hx.1).trans (hbase.subset hy.1).symm
    · exact F.injective s hs hcard hx.2 hy.2 he
  have him : g '' (T.diskDualBase s ×ˢ I) = T.dualRegion s := by
    rw [← F.image_eq s hs hcard]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(s.centroid ℝ id, t), ⟨hbase.symm.subset rfl, ht⟩, rfl⟩
  have hcentral : ∀ x ∈ T.diskDualBase s, g (x, 0) = x := by
    intro x hx
    exact (F.central s hs hcard).trans (hbase.subset hx).symm
  have hnotrim : s.centroid ℝ id ∉ T.dualRegionRim s := by
    intro hx
    have ht := (F.rim s hs hcard 0 (by norm_num)).mp
      ((F.central s hs hcard).symm ▸ hx)
    norm_num at ht
  refine ⟨⟨g, hg, hi, him, hcentral, ?_, ?_, ?_, ?_⟩, fun _ => rfl⟩
  · intro x hx
    exact iff_of_false (fun hf => hf.2 (hinside (him.subset (mem_image_of_mem g hx))))
      (fun hf => hf.2 (hinside hx.1.1))
  · intro x hx
    have hn : x.1 ∉ T.dualRegionRim s ∩ D := by
      intro h
      exact hnotrim ((hbase.subset hx.1) ▸ h.1)
    simpa only [g, hn, false_or] using F.rim s hs hcard x.2 hx.2
  · intro p hp x hx
    exact F.positive s hs hcard p hp x.2 hx.2
  · intro p hp x hx
    exact F.negative s hs hcard p hp x.2 hx.2

end PoincareConjecture.M76.HamiltonIndexOne
