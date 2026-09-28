import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspaceConnectedLinks
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalFacetIncidence
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarConnectedLinks

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

theorem isConnected_faceLink_of_original_interior_chart
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card < 3)
    {p : E} (hps : p ∈ s) (hpfront : (g p : X) ∉ frontier R)
    (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    IsConnected (K.faceLink s).space := by
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
  have hS : S.faces.Finite := hK.subset (fun _ ht => ht.1)
  have hJ : J.faces.Finite := hface.embeddedImage_finite hinj hS
  have hsJ : s.image a ∈ J.faces :=
    (hface.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
  have hcardJ : (s.image a).card = s.card :=
    Finset.card_image_iff.mpr (hinj.mono (S.subset_space hsS))
  have hpos : 0 < s.card := Finset.card_pos.mpr ⟨p, hps⟩
  have hdim : Module.finrank ℝ (affineSpan ℝ (s.image a : Set V3)).direction =
      s.card - 1 := J.finrank_faceDirection_of_card hsJ (by omega)
  have hcodim : Module.finrank ℝ (affineSpan ℝ (s.image a : Set V3)).direction + 1 <
      Module.finrank ℝ V3 := by
    have hdimV : Module.finrank ℝ V3 = 3 := by simp
    rw [hdim, hdimV]
    omega
  have hintJ : a p ∈ interior J.space := by
    rw [hface.embeddedImage_space hinj]
    exact hint
  have hlink := J.isConnected_faceLink_of_hull_meets_interior hJ hsJ hcodim
    ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hintJ⟩
  have hsourceLink := hface.isConnected_faceLink_of_embeddedImage hinj hS hsS hlink
  have hSl : S.faceLink s = K.faceLink s := by
    change (K.closedStar p).faceLink s = K.faceLink s
    rw [← K.closedFaceStar_singleton_eq_closedStar]
    exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hSl] at hsourceLink

theorem isConnected_faceLink_of_original_boundary_chart
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    {s : Finset E} (hs : s ∈ K.faces)
    (hsfront : ∀ q ∈ s, (g q : X) ∈ frontier R)
    {p : E} (hps : p ∈ s) (B : OpenPartialHomeomorph X V3)
    (hsource : MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source)
    (hface : (K.closedStar p).AffineOnFaces (fun z => B (g z)))
    (hregion : B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    IsConnected (K.faceLink s).space := by
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
  obtain ⟨hinj, O, hO, hpO, hOB, hOR⟩ :=
    K.exists_original_open_neighborhood_of_closedStar hK H g hg hp B hsource
  let J := hface.embeddedImage hinj
  have hS : S.faces.Finite := hK.subset (fun _ ht => ht.1)
  have hJ : J.faces.Finite := hface.embeddedImage_finite hinj hS
  have hsJ : s.image a ∈ J.faces :=
    (hface.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro h
    have hval : ell.toAffineMap.linear v = 1 := hv
    rw [h] at hval
    exact zero_ne_one hval
  have hfront := B.isImage_frontier_of_affine_nonneg ell hell hhalf
  have hzero : ∀ z ∈ affineSpan ℝ (s.image a : Set V3), ell z = 0 := by
    have hvert : EqOn ell.toAffineMap (AffineMap.const ℝ V3 0) (s.image a : Set V3) := by
      rintro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      exact (hfront.apply_mem_iff (hsource (S.subset_space hsS hq))).mpr (hsfront q hq)
    exact fun z hz => AffineMap.eqOn_affineSpan hvert hz
  have hlink : IsConnected (J.faceLink (s.image a)).space := by
    apply J.isConnected_faceLink_of_halfspace_patch hJ hsJ ell hell
      (V := B '' O)
    · rw [hface.embeddedImage_space hinj]
      rintro _ ⟨z, hz, rfl⟩
      exact (hhalf (g z) (hsource hz)).mp (g z).property
    · exact hzero
    · exact B.isOpen_image_of_subset_source hO hOB
    · rw [hface.embeddedImage_space hinj]
      rintro z ⟨⟨x, hxO, rfl⟩, hxell⟩
      obtain ⟨y, hy, hyx⟩ := hOR ⟨hxO, (hhalf x (hOB hxO)).mpr hxell⟩
      exact ⟨y, hy, congrArg B hyx⟩
    · exact ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩),
        mem_image_of_mem B hpO⟩
  have hsourceLink := hface.isConnected_faceLink_of_embeddedImage hinj hS hsS hlink
  have hSl : S.faceLink s = K.faceLink s := by
    change (K.closedStar p).faceLink s = K.faceLink s
    rw [← K.closedFaceStar_singleton_eq_closedStar]
    exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hSl] at hsourceLink

theorem original_chart_stars_connected_links
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A : SimplicialComplex ℝ E) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    {R : Set X} (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hboundary : ∀ z ∈ K.space, (g z : X) ∈ frontier R ↔ z ∈ A.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))) :
    ∀ s ∈ K.faces, s.card < 3 → IsConnected (K.faceLink s).space := by
  intro s hs hscard
  by_cases hsA : s ∈ A.faces
  · obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
    have hp : p ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
    obtain ⟨B, hsource, hface, hregion⟩ := hstars p hp
    exact isConnected_faceLink_of_original_boundary_chart K hK H g hg hs
      (fun q hq => (hboundary q (K.subset_space hs hq)).mpr (A.subset_space hsA hq))
      hps B hsource hface hregion
  · obtain ⟨p, hps, hpA⟩ :=
      SimplicialComplex.exists_vertex_off_full_subcomplex hAK hfull hs hsA
    have hp : p ∈ K.vertices := K.down_closed hs
      (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
    obtain ⟨B, hsource, hface, hregion⟩ := hstars p hp
    exact isConnected_faceLink_of_original_interior_chart K hK H g hg hs hscard hps
      (fun h => hpA ((hboundary p (K.subset_space hs hps)).mp h)) B hsource hface hregion

end PoincareConjecture.M76
