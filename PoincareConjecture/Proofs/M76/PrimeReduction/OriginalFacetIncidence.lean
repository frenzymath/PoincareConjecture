import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryFacetLinks
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryMarks
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

theorem faceLink_ncard_eq_two_of_original_chart
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = 3)
    {p : E} (hps : p ∈ s) (hpfront : (g p : X) ∉ frontier R)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    (K.faceLink s).vertices.ncard = 2 := by
  classical
  have hp : p ∈ K.vertices := K.down_closed hs
    (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
  let a : E → V3 := fun z => B (g z)
  let S := K.closedStar p
  have hsS : s ∈ S.faces := ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
  have hpS : p ∈ S.space := S.subset_space hsS hps
  obtain ⟨hinj, V, hV, hpV, hcase⟩ :=
    exists_original_closedStar_image_neighborhood K hK H g hg hp B hsource hregion
  have hint : a p ∈ interior (a '' S.space) := by
    rcases hcase with hinside | ⟨ell, v, hv, hpatch, hhalf, hfront⟩
    · exact interior_maximal hinside hV hpV
    · have hnonneg : 0 ≤ ell (a p) := hhalf (mem_image_of_mem a hpS)
      have hne : ell (a p) ≠ 0 := fun h => hpfront ((hfront p hpS).mpr h)
      have hpos : 0 < ell (a p) := lt_of_le_of_ne hnonneg (Ne.symm hne)
      exact interior_maximal
        (fun z hz => hpatch ⟨hz.1, (show 0 < ell z from hz.2).le⟩)
        (hV.inter (isOpen_lt continuous_const ell.continuous)) ⟨hpV, hpos⟩
  let J := hface.embeddedImage hinj
  have hJ : J.faces.Finite := hface.embeddedImage_finite hinj
    (hK.subset (fun _ ht => ht.1))
  have hsJ : s.image a ∈ J.faces :=
    (hface.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
  have hcardJ : (s.image a).card = Module.finrank ℝ V3 := by
    rw [Finset.card_image_iff.mpr (hinj.mono (S.subset_space hsS)), hscard]
    simp
  have hintJ : a p ∈ interior J.space := by
    rw [hface.embeddedImage_space hinj]
    exact hint
  have hlink := J.faceLink_ncard_eq_two_of_hull_meets_interior hJ hsJ hcardJ
    ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hintJ⟩
  rw [hface.ncard_embeddedImage_faceLink hinj hsS] at hlink
  have hSl : S.faceLink s = K.faceLink s := by
    change (K.closedStar p).faceLink s = K.faceLink s
    rw [← K.closedFaceStar_singleton_eq_closedStar]
    exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hSl] at hlink

theorem faceLink_ncard_eq_one_of_original_chart
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = 3)
    (hsfront : ∀ q ∈ s, (g q : X) ∈ frontier R)
    {p : E} (hps : p ∈ s) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))
    (hcoface : ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) :
    (K.faceLink s).vertices.ncard = 1 := by
  classical
  have hp : p ∈ K.vertices := K.down_closed hs
    (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
  let a : E → V3 := fun z => B (g z)
  let S := K.closedStar p
  have hsS : s ∈ S.faces := ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
  have hpS : p ∈ S.space := S.subset_space hsS hps
  rcases hregion with hinterior | ⟨ell, v, hv, hhalf⟩
  · exact False.elim ((hsfront p hps).2
      (interior_maximal hinterior B.open_source (hsource hpS)))
  have hinj := (K.exists_original_open_neighborhood_of_closedStar
    hK H g hg hp B hsource).1
  let J := hface.embeddedImage hinj
  have hsJ : s.image a ∈ J.faces :=
    (hface.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
  have hcardJ : (s.image a).card = Module.finrank ℝ V3 := by
    rw [Finset.card_image_iff.mpr (hinj.mono (S.subset_space hsS)), hscard]
    simp
  obtain ⟨t, ht, hst, htcard⟩ := hcoface
  have hpt : p ∈ t := hst hps
  have htS : t ∈ S.faces := ⟨ht, by simpa only [Finset.insert_eq_of_mem hpt] using ht⟩
  have htJ : t.image a ∈ J.faces :=
    (hface.image_mem_embeddedImage_iff hinj (S.subset_space htS)).mpr htS
  have htcardJ : (t.image a).card = Module.finrank ℝ V3 + 1 := by
    rw [Finset.card_image_iff.mpr (hinj.mono (S.subset_space htS)), htcard]
    simp
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    exact zero_ne_one hval
  have hfront := B.isImage_frontier_of_affine_nonneg ell hell hhalf
  have hJhalf : J.space ⊆ {z | 0 ≤ ell z} := by
    rw [hface.embeddedImage_space hinj]
    rintro z ⟨q, hq, rfl⟩
    exact (hhalf (g q) (hsource hq)).mp (g q).property
  have hzero : ∀ z ∈ convexHull ℝ (s.image a : Set V3), ell z = 0 := by
    have hvert : EqOn ell.toAffineMap (AffineMap.const ℝ V3 0) (s.image a : Set V3) := by
      rintro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      exact (hfront.apply_mem_iff (hsource (S.subset_space hsS hq))).mpr (hsfront q hq)
    intro z hz
    exact AffineMap.eqOn_affineSpan hvert (convexHull_subset_affineSpan _ hz)
  have hlink := J.faceLink_ncard_eq_one_of_halfspace hsJ hcardJ htJ
    (Finset.image_subset_image hst) htcardJ ell v hv hJhalf hzero
  rw [hface.ncard_embeddedImage_faceLink hinj hsS] at hlink
  have hSl : S.faceLink s = K.faceLink s := by
    change (K.closedStar p).faceLink s = K.faceLink s
    rw [← K.closedFaceStar_singleton_eq_closedStar]
    exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hSl] at hlink

theorem original_chart_stars_facet_incidence
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A : SimplicialComplex ℝ E) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hboundary : ∀ z ∈ K.space, (g z : X) ∈ frontier R ↔ z ∈ A.space)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))) :
    ∀ s ∈ K.faces, s.card = 3 →
      (s ∈ A.faces → (K.faceLink s).vertices.ncard = 1) ∧
      (s ∉ A.faces → (K.faceLink s).vertices.ncard = 2) := by
  intro s hs hscard
  constructor
  · intro hsA
    obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
    have hp : p ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
    obtain ⟨B, hsource, hface, hregion⟩ := hstars p hp
    apply faceLink_ncard_eq_one_of_original_chart K hK H g hg hs hscard
      (fun q hq => (hboundary q (K.subset_space hs hq)).mpr (A.subset_space hsA hq))
      hps B hsource hface hregion (hpure s hs)
  · intro hsA
    obtain ⟨p, hps, hpA⟩ :=
      SimplicialComplex.exists_vertex_off_full_subcomplex hAK hfull hs hsA
    have hp : p ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
    obtain ⟨B, hsource, hface, hregion⟩ := hstars p hp
    exact faceLink_ncard_eq_two_of_original_chart K hK H g hg hs hscard hps
      (fun h => hpA ((hboundary p (K.subset_space hs hps)).mp h)) B hsource hface hregion

end PoincareConjecture.M76
