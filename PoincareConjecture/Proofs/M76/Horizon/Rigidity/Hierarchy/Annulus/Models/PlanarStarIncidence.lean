import PoincareConjecture.Proofs.M76.PrimeReduction.LocalHalfspaceDensity
import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryFacetLinks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.HalfspaceConnectedLinks
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarConnectedLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryMarks









set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

local notation "V2" => (Fin 2 → ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_triangular_coface_of_planar_halfspace_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hstars : ∀ p ∈ K.vertices, ∃ (a : E → V2) (V : Set V2),
      (K.closedStar p).AffineOnFaces a ∧ InjOn a (K.closedStar p).space ∧
      IsOpen V ∧ a p ∈ V ∧
      (V ⊆ a '' (K.closedStar p).space ∨
        ∃ (ell : V2 →ᴬ[ℝ] ℝ) (v : V2), ell.contLinear v = 1 ∧
          V ∩ {z | 0 ≤ ell z} ⊆ a '' (K.closedStar p).space ∧
          a '' (K.closedStar p).space ⊆ {z | 0 ≤ ell z})) :
    ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3 := by
  classical
  intro s hs
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
  have hp : p ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
  obtain ⟨a, V, hf, hinj, hV, hpV, hcase⟩ := hstars p hp
  let S := K.closedStar p
  have hS : S.faces.Finite := finite_closedStar_faces hK p
  have hsS : s ∈ S.faces := ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
  let J := hf.embeddedImage hinj
  have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hS
  have hJs : J.space = a '' S.space := hf.embeddedImage_space hinj
  have hsJ : s.image a ∈ J.faces :=
    (hf.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
  obtain ⟨z, hzs, hzV⟩ :=
    (convex_convexHull ℝ (s.image a : Set V2)).intrinsicInterior_inter_open_nonempty
      hV ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hpV⟩
  have hzJ : z ∈ J.space := J.convexHull_subset_space hsJ (intrinsicInterior_subset hzs)
  have hzcl : z ∈ closure (interior J.space) := by
    rw [hJs]
    rcases hcase with hinside | ⟨ell, v, hv, hpatch, hhalf⟩
    · exact subset_closure (interior_maximal hinside hV hzV)
    · exact PoincareConjecture.M76.mem_closure_interior_of_affine_halfspace_patch
        hV ell v hv hpatch hzV (hhalf (hJs.subset hzJ))
  obtain ⟨t, ht, htcard, hzt⟩ := J.exists_full_face_of_mem_closure_interior hJ hzcl
  have hst := J.subset_of_mem_intrinsicInterior_face hsJ ht hzs hzt
  rw [hf.embeddedImage_faces hinj] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  refine ⟨u, hu.1, ?_, ?_⟩
  · intro v hvs
    obtain ⟨w, hwu, hwv⟩ := Finset.mem_image.mp
      (hst (Finset.mem_image.mpr ⟨v, hvs, rfl⟩))
    have hwveq := hinj (S.subset_space hu hwu) (S.subset_space hsS hvs) hwv
    exact hwveq ▸ hwu
  · have hcard := (Finset.card_image_iff.mpr (hinj.mono (S.subset_space hu))).symm.trans htcard
    simpa using hcard

open Classical in
theorem marked_surface_incidence_of_planar_halfspace_stars
    (K B : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hBK : B ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ B.vertices) → s ∈ B.faces)
    (hstars : ∀ p ∈ K.vertices, ∃ (a : E → V2) (V : Set V2),
      (K.closedStar p).AffineOnFaces a ∧ InjOn a (K.closedStar p).space ∧
      IsOpen V ∧ a p ∈ V ∧
      ((V ⊆ a '' (K.closedStar p).space ∧ Disjoint (K.closedStar p).space B.space) ∨
        ∃ (ell : V2 →ᴬ[ℝ] ℝ) (v : V2), ell.contLinear v = 1 ∧
          V ∩ {z | 0 ≤ ell z} ⊆ a '' (K.closedStar p).space ∧
          a '' (K.closedStar p).space ⊆ {z | 0 ≤ ell z} ∧
          ∀ x ∈ (K.closedStar p).space, x ∈ B.space ↔ ell (a x) = 0)) :
    (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3) ∧
      (∀ s ∈ K.faces, s.card = 2 →
        (K.faceLink s).vertices.ncard = if s ∈ B.faces then 1 else 2) ∧
      ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space := by
  classical
  have hpure := K.exists_triangular_coface_of_planar_halfspace_stars hK (by
    intro p hp
    obtain ⟨a, V, hf, hi, hV, hpV, hcase⟩ := hstars p hp
    refine ⟨a, V, hf, hi, hV, hpV, ?_⟩
    rcases hcase with h | ⟨ell, v, hv, hpatch, hhalf, _⟩
    · exact Or.inl h.1
    · exact Or.inr ⟨ell, v, hv, hpatch, hhalf⟩)
  refine ⟨hpure, ?_, ?_⟩
  · intro s hs hscard
    obtain ⟨p, hps, hpmark⟩ : ∃ p ∈ s, (p ∈ B.vertices ↔ s ∈ B.faces) := by
      by_cases hsB : s ∈ B.faces
      · obtain ⟨p, hp⟩ := K.nonempty_of_mem_faces hs
        exact ⟨p, hp, iff_of_true (B.face_subset_vertices hsB hp) hsB⟩
      · obtain ⟨p, hp, hpB⟩ := exists_vertex_off_full_subcomplex hBK hfull hs hsB
        exact ⟨p, hp, iff_of_false (fun hv => hpB (B.vertices_subset_space hv)) hsB⟩
    have hp : p ∈ K.vertices := K.face_subset_vertices hs hps
    obtain ⟨a, V, hf, hinj, hV, hpV, hcase⟩ := hstars p hp
    let S := K.closedStar p
    have hS : S.faces.Finite := finite_closedStar_faces hK p
    have hsS : s ∈ S.faces := ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
    have hpS : p ∈ S.space := S.subset_space hsS hps
    let J := hf.embeddedImage hinj
    have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hS
    have hJs : J.space = a '' S.space := hf.embeddedImage_space hinj
    have hsJ : s.image a ∈ J.faces :=
      (hf.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
    have hcardJ : (s.image a).card = Module.finrank ℝ V2 := by
      rw [Finset.card_image_iff.mpr (hinj.mono (S.subset_space hsS)), hscard]
      simp
    have hSl : S.faceLink s = K.faceLink s := by
      rw [show S = K.closedFaceStar {p} from (K.closedFaceStar_singleton_eq_closedStar p).symm]
      exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
    have htwo (hint : a p ∈ interior J.space) : (K.faceLink s).vertices.ncard = 2 := by
      have h := J.faceLink_ncard_eq_two_of_hull_meets_interior hJ hsJ hcardJ
        ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hint⟩
      rwa [hf.ncard_embeddedImage_faceLink hinj hsS, hSl] at h
    rcases hcase with ⟨hinside, hdis⟩ | ⟨ell, v, hv, hpatch, hhalf, hmark⟩
    · have hsB : s ∉ B.faces := fun hsB =>
        disjoint_left.mp hdis hpS (B.vertices_subset_space (hpmark.mpr hsB))
      rw [if_neg hsB]
      apply htwo
      rw [hJs]
      exact interior_maximal hinside hV hpV
    · by_cases hsB : s ∈ B.faces
      · rw [if_pos hsB]
        obtain ⟨t, ht, hst, htcard⟩ := hpure s hs
        have hpt : p ∈ t := hst hps
        have htS : t ∈ S.faces := ⟨ht, by simpa only [Finset.insert_eq_of_mem hpt] using ht⟩
        have htJ : t.image a ∈ J.faces :=
          (hf.image_mem_embeddedImage_iff hinj (S.subset_space htS)).mpr htS
        have htcardJ : (t.image a).card = Module.finrank ℝ V2 + 1 := by
          rw [Finset.card_image_iff.mpr (hinj.mono (S.subset_space htS)), htcard]
          simp
        have hzero : ∀ z ∈ convexHull ℝ (s.image a : Set V2), ell z = 0 := by
          have hvert : EqOn ell.toAffineMap (AffineMap.const ℝ V2 0) (s.image a : Set V2) := by
            rintro z hz
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
            exact (hmark x (S.subset_space hsS hx)).mp (B.subset_space hsB hx)
          exact fun z hz => AffineMap.eqOn_affineSpan hvert (convexHull_subset_affineSpan _ hz)
        have hcount := J.faceLink_ncard_eq_one_of_halfspace hsJ hcardJ htJ
          (Finset.image_subset_image hst) htcardJ ell v hv
          (by rw [hJs]; exact hhalf) hzero
        rwa [hf.ncard_embeddedImage_faceLink hinj hsS, hSl] at hcount
      · rw [if_neg hsB]
        have hpB : p ∉ B.space := fun hpB => hsB (hpmark.mp (by
          exact (vertex_mem_subcomplex_space_iff hBK hp).mp hpB))
        have hpos : 0 < ell (a p) := lt_of_le_of_ne
          (hhalf (mem_image_of_mem a hpS)) (Ne.symm (fun hz => hpB ((hmark p hpS).mpr hz)))
        apply htwo
        rw [hJs]
        exact interior_maximal
          (fun z hz => hpatch ⟨hz.1, (show 0 < ell z from hz.2).le⟩)
          (hV.inter (isOpen_lt continuous_const ell.continuous)) ⟨hpV, hpos⟩
  · intro p hp
    obtain ⟨a, V, hf, hinj, hV, hpV, hcase⟩ := hstars p hp
    let S := K.closedStar p
    have hS : S.faces.Finite := finite_closedStar_faces hK p
    have hpface : {p} ∈ K.faces := hp
    have hsS : {p} ∈ S.faces := ⟨hpface, by simpa using hpface⟩
    have hpS : p ∈ S.space := S.subset_space hsS (Finset.mem_singleton_self p)
    let J := hf.embeddedImage hinj
    have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hS
    have hJs : J.space = a '' S.space := hf.embeddedImage_space hinj
    have hsJ : ({p} : Finset E).image a ∈ J.faces :=
      (hf.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
    have hSl : S.faceLink {p} = K.faceLink {p} := by
      rw [show S = K.closedFaceStar {p} from (K.closedFaceStar_singleton_eq_closedStar p).symm]
      exact K.closedFaceStar_faceLink_of_subset (Finset.Subset.refl _)
    have hconn (hint : a p ∈ interior J.space) :
        IsConnected (J.faceLink (({p} : Finset E).image a)).space := by
      apply J.isConnected_faceLink_of_hull_meets_interior hJ hsJ
      · rw [J.finrank_faceDirection_of_card hsJ (n := 0) (by simp)]
        simp
      · exact ⟨a p, by simp, hint⟩
    have hjconn : IsConnected (J.faceLink (({p} : Finset E).image a)).space := by
      rcases hcase with ⟨hinside, _⟩ | ⟨ell, v, hv, hpatch, hhalf, _⟩
      · apply hconn
        rw [hJs]
        exact interior_maximal hinside hV hpV
      · by_cases hz : ell (a p) = 0
        · have hell : ell.toAffineMap.linear ≠ 0 := by
            intro h
            have he : ell.toAffineMap.linear v = 1 := hv
            rw [h, LinearMap.zero_apply] at he
            exact zero_ne_one he
          refine J.isConnected_faceLink_of_halfspace_patch hJ hsJ ell hell
            (by rw [hJs]; exact hhalf) ?_ hV (by rw [hJs]; exact hpatch) ?_
          · have hvert : EqOn ell.toAffineMap (AffineMap.const ℝ V2 0)
                (({p} : Finset E).image a : Set V2) := by
              intro z hz'
              have hzp : z = a p := by simpa using hz'
              subst z
              exact hz
            exact fun z hz' => AffineMap.eqOn_affineSpan hvert hz'
          · exact ⟨a p, by simp, hpV⟩
        · have hpos := lt_of_le_of_ne (hhalf (mem_image_of_mem a hpS)) (Ne.symm hz)
          apply hconn
          rw [hJs]
          exact interior_maximal
            (fun z hz => hpatch ⟨hz.1, (show 0 < ell z from hz.2).le⟩)
            (hV.inter (isOpen_lt continuous_const ell.continuous)) ⟨hpV, hpos⟩
    have hc := hf.isConnected_faceLink_of_embeddedImage hinj hS hsS hjconn
    rwa [hSl] at hc

end Geometry.SimplicialComplex
