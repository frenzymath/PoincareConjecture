import PoincareConjecture.Proofs.M76.Mathlib.CenteredOriginalEventBody
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_original_event_body_in_centered_coordinates
    {ι : Type*} [Finite ι] [Nonempty ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    {p : E} (hp : p ∈ K.space) (e : E ≃ᴬ[ℝ] E) (hep : e p = 0)
    {U : Set E} (hU : IsOpen U) (hpU : p ∈ U) (c : E ≃L[ℝ] (ι → ℝ)) :
    let K0 := (K.affineOnFaces_affine e.toContinuousAffineMap).embeddedImage e.injective.injOn
    ∃ (M : SimplicialComplex ℝ E) (C : Set E)
      (L : (ι ⊕ ι) → E →ₗ[ℝ] ℝ) (J : SimplicialComplex ℝ E),
      K0.faces.Finite ∧ K0.space = e '' K.space ∧
      (∀ s ∈ K0.faces, s.card ≤ 3) ∧
      M.faces.Finite ∧ M.space = K0.space ∧ (0 : E) ∈ M.vertices ∧
      (∀ s ∈ M.faces, ∃ t ∈ M.faces, t.card = 3 ∧ s ⊆ t) ∧
      (∀ s ∈ M.faces, s.card = 2 →
        {t : Finset E | t ∈ M.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) ∧
      (M.link 0).vertexAbstractComplex.edgeGraph.Connected ∧
      IsCompact C ∧ Convex ℝ C ∧ (0 : E) ∈ interior C ∧ C ⊆ e '' U ∧
      Disjoint C (M.link 0).space ∧
      M.space ∩ C = (M.closedStar 0).space ∩ C ∧
      (∀ s ∈ K0.faces, (convexHull ℝ (s : Set E) ∩ C).Nonempty →
        (0 : E) ∈ convexHull ℝ (s : Set E)) ∧
      (∀ i, L i ≠ 0) ∧ C = {x | ∀ i, L i x ≤ 1} ∧
      J.faces.Finite ∧ J.space = frontier C ∧
      IsCompact (e.symm '' C) ∧ Convex ℝ (e.symm '' C) ∧
      p ∈ interior (e.symm '' C) ∧ e.symm '' C ⊆ U ∧
      ∀ s ∈ K.faces, (convexHull ℝ (s : Set E) ∩ (e.symm '' C)).Nonempty →
        p ∈ convexHull ℝ (s : Set E) := by
  classical
  let hf := K.affineOnFaces_affine e.toContinuousAffineMap
  let K0 := hf.embeddedImage e.injective.injOn
  have hK0 : K0.faces.Finite := hf.embeddedImage_finite e.injective.injOn hK
  have hK0space : K0.space = e '' K.space := hf.embeddedImage_space e.injective.injOn
  have hpure0 : ∀ s ∈ K0.faces, ∃ t ∈ K0.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, hcard⟩ := hf.embeddedImage_pure e.injective.injOn
      (fun s hs => (hpure s hs).imp fun _ h => ⟨h.1, h.2.2, h.2.1⟩) s hs
    exact ⟨t, ht, hcard, hst⟩
  have hcofaces0 : ∀ s ∈ K0.faces, s.card = 2 →
      {t : Finset E | t ∈ K0.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 :=
    hf.embeddedImage_coface_count e.injective.injOn hcofaces
  have hlinks0 : ∀ q ∈ K0.vertices, IsConnected (K0.link q).space := by
    intro q hq
    rw [hf.embeddedImage_vertices e.injective.injOn] at hq
    obtain ⟨v, hv, rfl⟩ := hq
    rw [hf.embeddedImage_link_space e.injective.injOn hv]
    exact (hlinks v hv).image e e.continuous.continuousOn
  have hzeroK0 : (0 : E) ∈ K0.space := hK0space.symm.subset ⟨p, hp, hep⟩
  obtain ⟨M, C, L, J, hM, hMK0, hzeroM, hpureM, hcofacesM, hconnM,
      hC, hcv, hzeroC, hCU, hdisj, hlocal, hfaceC, hL, hrep, hJ, hJC⟩ :=
    K0.exists_centered_original_event_body hK0 hpure0 hcofaces0 hlinks0 hzeroK0
      (e.toHomeomorph.isOpenMap U hU) ⟨p, hpU, hep⟩ c
  have hbound0 (s : Finset E) (hs : s ∈ K0.faces) : s.card ≤ 3 := by
    obtain ⟨t, _, htc, hst⟩ := hpure0 s hs
    exact (Finset.card_le_card hst).trans_eq htc
  have hbackzero : e.symm 0 = p := by
    rw [← hep, e.symm_apply_apply]
  have hpbody : p ∈ interior (e.symm '' C) := by
    exact (e.symm.toHomeomorph.image_interior C).subset ⟨0, hzeroC, hbackzero⟩
  have hbodyU : e.symm '' C ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hCU hy
    change e z = y at hzy
    rwa [← hzy, e.symm_apply_apply]
  refine ⟨M, C, L, J, hK0, hK0space, hbound0, hM, hMK0, hzeroM, hpureM,
    hcofacesM, hconnM, hC, hcv, hzeroC, hCU, hdisj, hlocal, hfaceC, hL,
    hrep, hJ, hJC, hC.image e.symm.continuous,
    hcv.affine_image e.symm.toAffineEquiv.toAffineMap, hpbody, hbodyU, ?_⟩
  intro s hs hmeet
  obtain ⟨x, hxs, y, hy, hyx⟩ := hmeet
  have hexy : e x = y := by rw [← hyx, e.apply_symm_apply]
  have hs0 : s.image e ∈ K0.faces := by
    rw [hf.embeddedImage_faces e.injective.injOn]
    exact mem_image_of_mem _ hs
  have hexs : e x ∈ convexHull ℝ ((s.image e : Finset E) : Set E) := by
    have hhull : e '' convexHull ℝ (s : Set E) = convexHull ℝ (e '' (s : Set E)) :=
      hf.image_convexHull hs
    rw [Finset.coe_image, ← hhull]
    exact mem_image_of_mem e hxs
  have hz := hfaceC (s.image e) hs0 ⟨e x, hexs, hexy.symm ▸ hy⟩
  have hhull : e '' convexHull ℝ (s : Set E) = convexHull ℝ (e '' (s : Set E)) :=
    hf.image_convexHull hs
  rw [Finset.coe_image, ← hhull] at hz
  obtain ⟨z, hzs, hze⟩ := hz
  exact (e.injective (hze.trans hep.symm)) ▸ hzs

end Geometry.SimplicialComplex
