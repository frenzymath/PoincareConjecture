import PoincareConjecture.Proofs.M76.Mathlib.CenteredDerivedSurface
import PoincareConjecture.Proofs.M76.Mathlib.OriginalConnectorBody
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_original_connector_body_in_centered_coordinates
    {ι : Type*} [Finite ι] [Nonempty ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = 3)
    {S U : Set E} (hS : IsCompact S) (hcvS : Convex ℝ S)
    (hSin : S ⊆ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {q : E} (hqS : q ∈ S) (e : E ≃ᴬ[ℝ] E) (heq : e q = 0)
    (hU : IsOpen U) (hSU : S ⊆ U) (c : E ≃L[ℝ] (ι → ℝ)) :
    let K0 := (K.affineOnFaces_affine e.toContinuousAffineMap).embeddedImage e.injective.injOn
    ∃ (M : SimplicialComplex ℝ E) (C : Set E)
      (L : Finset (E →ₗ[ℝ] ℝ)) (J : SimplicialComplex ℝ E),
      K0.faces.Finite ∧ K0.space = e '' K.space ∧
      (∀ t ∈ K0.faces, t.card ≤ 3) ∧
      M.faces.Finite ∧ M.space = K0.space ∧ (0 : E) ∈ M.vertices ∧
      (∀ t ∈ M.faces, ∃ u ∈ M.faces, u.card = 3 ∧ t ⊆ u) ∧
      (∀ t ∈ M.faces, t.card = 2 →
        {u : Finset E | u ∈ M.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2) ∧
      (M.link 0).vertexAbstractComplex.edgeGraph.Connected ∧
      (M.closedStar 0).space = e '' convexHull ℝ (s : Set E) ∧
      (M.link 0).space = e '' intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ∧
      IsCompact C ∧ Convex ℝ C ∧ (0 : E) ∈ interior C ∧
      e '' S ⊆ interior C ∧ C ⊆ e '' U ∧ Disjoint C (M.link 0).space ∧
      M.space ∩ C = (M.closedStar 0).space ∩ C ∧
      (∀ t ∈ K0.faces, (convexHull ℝ (t : Set E) ∩ C).Nonempty →
        (0 : E) ∈ convexHull ℝ (t : Set E)) ∧
      L.Nonempty ∧ (∀ A ∈ L, A ≠ 0) ∧ C = {x | ∀ A ∈ L, A x ≤ 1} ∧
      J.faces.Finite ∧ J.space = frontier C ∧
      IsCompact (e.symm '' C) ∧ Convex ℝ (e.symm '' C) ∧
      q ∈ interior (e.symm '' C) ∧ S ⊆ interior (e.symm '' C) ∧ e.symm '' C ⊆ U ∧
      ∀ t ∈ K.faces, (convexHull ℝ (t : Set E) ∩ (e.symm '' C)).Nonempty →
        q ∈ convexHull ℝ (t : Set E) := by
  classical
  let hf := K.affineOnFaces_affine e.toContinuousAffineMap
  let K0 := hf.embeddedImage e.injective.injOn
  let s0 := s.image e
  have hK0 : K0.faces.Finite := hf.embeddedImage_finite e.injective.injOn hK
  have hK0space : K0.space = e '' K.space := hf.embeddedImage_space e.injective.injOn
  have hpure0 : ∀ t ∈ K0.faces, ∃ u ∈ K0.faces, u.card = 3 ∧ t ⊆ u := by
    intro t ht
    obtain ⟨u, hu, htu, hcard⟩ := hf.embeddedImage_pure e.injective.injOn
      (fun t ht => (hpure t ht).imp fun _ h => ⟨h.1, h.2.2, h.2.1⟩) t ht
    exact ⟨u, hu, hcard, htu⟩
  have hcofaces0 : ∀ t ∈ K0.faces, t.card = 2 →
      {u : Finset E | u ∈ K0.faces ∧ u.card = 3 ∧ t ⊆ u}.ncard = 2 :=
    hf.embeddedImage_coface_count e.injective.injOn hcofaces
  have hlinks0 : ∀ p ∈ K0.vertices, IsConnected (K0.link p).space := by
    intro p hp
    rw [hf.embeddedImage_vertices e.injective.injOn] at hp
    obtain ⟨v, hv, rfl⟩ := hp
    rw [hf.embeddedImage_link_space e.injective.injOn hv]
    exact (hlinks v hv).image e e.continuous.continuousOn
  have hbound0 (t : Finset E) (ht : t ∈ K0.faces) : t.card ≤ 3 := by
    obtain ⟨u, _, huc, htu⟩ := hpure0 t ht
    exact (Finset.card_le_card htu).trans_eq huc
  have hs0 : s0 ∈ K0.faces := by
    rw [hf.embeddedImage_faces e.injective.injOn]
    exact mem_image_of_mem _ hs
  have hcard0 : s0.card = 3 :=
    (Finset.card_image_iff.mpr e.injective.injOn).trans hscard
  have hhull : convexHull ℝ (s0 : Set E) = e '' convexHull ℝ (s : Set E) := by
    dsimp only [s0]
    rw [Finset.coe_image]
    exact (hf.image_convexHull hs).symm
  have hSin0 : e '' S ⊆ intrinsicInterior ℝ (convexHull ℝ (s0 : Set E)) := by
    rw [hhull, e.intrinsicInterior_image]
    exact image_mono hSin
  have hzeroS : (0 : E) ∈ e '' S := ⟨q, hqS, heq⟩
  obtain ⟨M, hM, hMK0, hzeroM, hpureM, hcofacesM, hconnM, hexact⟩ :=
    K0.exists_centered_derived_surface_at_face_point hK0 hpure0 hcofaces0 hlinks0
      ⟨s0, hs0⟩ (hSin0 hzeroS)
  obtain ⟨hstar, hlink⟩ := hexact hcard0
  have hmax0 (t : Finset E) (ht : t ∈ K0.faces) (hst : s0 ⊆ t) : t = s0 :=
    (Finset.eq_of_subset_of_card_le hst (by simpa only [hcard0] using hbound0 t ht)).symm
  obtain ⟨C, L, J, hC, hcv, hzeroC, hSC, hCU, hdisj, hlocal, hfaceC,
      hLne, hL, hrep, hJ, hJC⟩ :=
    K0.exists_compact_convex_maximal_face_body hK0 hs0 hmax0
      (hS.image e.continuous) (hcvS.affine_image e.toAffineEquiv.toAffineMap)
      hzeroS hSin0 (e.toHomeomorph.isOpenMap U hU) (image_mono hSU)
      M hMK0 hstar hlink c
  have hstarOriginal : (M.closedStar 0).space = e '' convexHull ℝ (s : Set E) :=
    hstar.trans hhull
  have hlinkOriginal : (M.link 0).space =
      e '' intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    rw [hlink, hhull, e.intrinsicFrontier_image]
  have hSbody : S ⊆ interior (e.symm '' C) := by
    intro x hx
    exact (e.symm.toHomeomorph.image_interior C).subset
      ⟨e x, hSC (mem_image_of_mem e hx), e.symm_apply_apply x⟩
  have hbodyU : e.symm '' C ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hCU hy
    change e z = y at hzy
    rwa [← hzy, e.symm_apply_apply]
  refine ⟨M, C, L, J, hK0, hK0space, hbound0, hM, hMK0, hzeroM, hpureM,
    hcofacesM, hconnM, hstarOriginal, hlinkOriginal, hC, hcv, hzeroC, hSC,
    hCU, hdisj, hlocal, hfaceC, hLne, hL, hrep, hJ, hJC,
    hC.image e.symm.continuous, hcv.affine_image e.symm.toAffineEquiv.toAffineMap,
    hSbody hqS, hSbody, hbodyU, ?_⟩
  intro t ht hmeet
  obtain ⟨x, hxt, y, hy, hyx⟩ := hmeet
  have hexy : e x = y := by rw [← hyx, e.apply_symm_apply]
  have ht0 : t.image e ∈ K0.faces := by
    rw [hf.embeddedImage_faces e.injective.injOn]
    exact mem_image_of_mem _ ht
  have hext : e x ∈ convexHull ℝ ((t.image e : Finset E) : Set E) := by
    have hhullt : e '' convexHull ℝ (t : Set E) = convexHull ℝ (e '' (t : Set E)) :=
      hf.image_convexHull ht
    rw [Finset.coe_image, ← hhullt]
    exact mem_image_of_mem e hxt
  have hz := hfaceC (t.image e) ht0 ⟨e x, hext, hexy.symm ▸ hy⟩
  have hhullt : e '' convexHull ℝ (t : Set E) = convexHull ℝ (e '' (t : Set E)) :=
    hf.image_convexHull ht
  rw [Finset.coe_image, ← hhullt] at hz
  obtain ⟨z, hzt, hze⟩ := hz
  exact (e.injective (hze.trans heq.symm)) ▸ hzt

end Geometry.SimplicialComplex
