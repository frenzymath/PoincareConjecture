import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Maps.ConvexBoundaryConeHomotopy











set_option autoImplicit false

open Set Geometry NormedSpace unitInterval

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem affineOnFaces_affine_transport
    {K : SimplicialComplex ℝ E} {b : E → F} (hb : K.AffineOnFaces b)
    (T : E ≃ᴬ[ℝ] E) :
    ((show K.AffineOnFaces (T : E → E) from
      K.affineOnFaces_affine T.toContinuousAffineMap).embeddedImage T.injective.injOn).AffineOnFaces
      (b ∘ T.symm) := by
  intro s hs
  rw [AffineOnFaces.embeddedImage_faces] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  obtain ⟨a, ha⟩ := hb t ht
  refine ⟨a.comp T.symm.toContinuousAffineMap, ?_⟩
  intro x hx
  rw [Finset.coe_image] at hx
  change x ∈ convexHull ℝ (T.toAffineEquiv.toAffineMap '' (t : Set E)) at hx
  rw [← T.toAffineEquiv.toAffineMap.image_convexHull] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using ha hy





theorem AffineOnFaces.exists_boundary_cone_at_homotopy_with_faces [Nontrivial E]
    {K : SimplicialComplex ℝ E} {b : E → F} (hb : K.AffineOnFaces b)
    (hK : K.faces.Finite) {S : Set E} (hS : IsCompact S) (hScv : Convex ℝ S)
    (c : E) (hc : c ∈ interior S) (hKS : K.space = frontier S)
    {W : Set F} (hW : Convex ℝ W) (f : E →ᴬ[ℝ] F) (hfW : MapsTo f S W)
    (B : C(I × frontier S, W))
    (hB0 : ∀ u : frontier S, (B (0, u) : F) = f u)
    (hB1 : ∀ u : frontier S, (B (1, u) : F) = b u)
    (a : F) (ha : a ∈ W) :
    ∃ (L : SimplicialComplex ℝ E) (g : E → F) (H : C(I × S, W)),
      L.faces.Finite ∧ L.space = S ∧ K ≤ L ∧ L.vertices = insert c K.vertices ∧
      (∀ s ∈ K.faces, insert c s ∈ L.faces) ∧
      (∀ s, s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces)) ∧
      L.AffineOnFaces g ∧ FinitePiecewiseAffineOn g S ∧ g c = a ∧
      EqOn g b (frontier S) ∧ MapsTo g S W ∧
      (∀ u ∈ frontier S, ∀ r ∈ Icc (0 : ℝ) 1,
        g ((1 - r) • c + r • u) = (1 - r) • a + r • b u) ∧
      (∀ x : S, (H (0, x) : F) = f x) ∧
      (∀ x : S, (H (1, x) : F) = g x) ∧
      ∀ (t : I) (u : frontier S),
        H (t, ⟨u, hS.isClosed.frontier_subset u.property⟩) = B (t, u) := by
  classical
  let T : E ≃ᴬ[ℝ] E := ContinuousAffineEquiv.constVAdd ℝ E (-c)
  have hTc : T c = 0 := by change -c + c = 0; exact neg_add_cancel c
  have hTi0 : T.symm 0 = c := T.injective (by rw [T.apply_symm_apply, hTc])
  let S0 := T '' S
  let hT : K.AffineOnFaces (T : E → E) := K.affineOnFaces_affine T.toContinuousAffineMap
  let K0 := hT.embeddedImage T.injective.injOn
  have hK0 : K0.faces.Finite := hT.embeddedImage_finite T.injective.injOn hK
  have hS0 : IsCompact S0 := hS.image T.continuous
  have hS0cv : Convex ℝ S0 := hScv.affine_image T.toAffineEquiv.toAffineMap
  have hzero : (0 : E) ∈ interior S0 := by
    rw [show S0 = T.toHomeomorph '' S from rfl, ← T.toHomeomorph.image_interior]
    exact ⟨c, hc, hTc⟩
  have hfront : T '' frontier S = frontier S0 := T.toHomeomorph.image_frontier S
  have hK0S : K0.space = frontier S0 := by
    rw [hT.embeddedImage_space, hKS, hfront]
  have hb0 : K0.AffineOnFaces (b ∘ T.symm) := affineOnFaces_affine_transport hb T
  let U : frontier S ≃ₜ frontier S0 :=
    (T.toHomeomorph.image (frontier S)).trans (Homeomorph.setCongr hfront)
  have hU (u : frontier S) : (U u : E) = T u := rfl
  have hUi (u : frontier S0) : (U.symm u : E) = T.symm u := by
    apply T.injective
    rw [T.apply_symm_apply]
    exact (hU (U.symm u)).symm.trans
      (congrArg Subtype.val (U.apply_symm_apply u))
  let B0 : C(I × frontier S0, W) :=
    B.comp ⟨fun z => (z.1, U.symm z.2),
      continuous_fst.prodMk (U.symm.continuous.comp continuous_snd)⟩
  let f0 := f.comp T.symm.toContinuousAffineMap
  have hf0W : MapsTo f0 S0 W := by
    rintro _ ⟨x, hx, rfl⟩
    change f (T.symm (T x)) ∈ W
    simpa using hfW hx
  have hB00 (u : frontier S0) : (B0 (0, u) : F) = f0 u := by
    change (B (0, U.symm u) : F) = f (T.symm u)
    rw [hB0, hUi]
  have hB01 (u : frontier S0) : (B0 (1, u) : F) = (b ∘ T.symm) u := by
    change (B (1, U.symm u) : F) = b (T.symm u)
    rw [hB1, hUi]
  obtain ⟨hlin, hrad, q, H0, hC0S, hq, hqPL, hq0, hqb, hqW, hqray,
    hH00, hH01, hH0B⟩ :=
    hb0.exists_convex_boundary_cone_homotopy hK0 hS0 hS0cv hzero hK0S
      hW f0 hf0W B0 hB00 hB01 a ha
  let C0 := K0.coneAtZero hlin hrad
  let hTi : C0.AffineOnFaces (T.symm : E → E) := C0.affineOnFaces_affine T.symm.toContinuousAffineMap
  let L := hTi.embeddedImage T.symm.injective.injOn
  let g : E → F := q ∘ T
  have hL : L.faces.Finite := hTi.embeddedImage_finite T.symm.injective.injOn
    (finite_coneAtZero_faces hK0 hlin hrad)
  have hLS : L.space = S := by
    rw [hTi.embeddedImage_space, hC0S]
    change T.symm '' (T '' S) = S
    rw [image_image]
    simp
  have hg : L.AffineOnFaces g := affineOnFaces_affine_transport hq T.symm
  have hKimage (s : Finset E) : (s.image T).image T.symm = s := by
    ext x
    simp
  have hKL : K ≤ L := by
    intro s hs
    change s ∈ L.faces
    rw [hTi.embeddedImage_faces]
    refine ⟨s.image T, le_coneAtZero hlin hrad ?_, hKimage s⟩
    change s.image T ∈ K0.faces
    rw [hT.embeddedImage_faces]
    exact ⟨s, hs, rfl⟩
  have hLvertices : L.vertices = insert c K.vertices := by
    rw [hTi.embeddedImage_vertices, coneAtZero_vertices, hT.embeddedImage_vertices,
      image_insert_eq, image_image, hTi0]
    simp
  have hcone (s : Finset E) (hs : s ∈ K.faces) : insert c s ∈ L.faces := by
    rw [hTi.embeddedImage_faces]
    refine ⟨insert 0 (s.image T), insert_zero_mem_coneAtZero_faces hlin hrad ?_, ?_⟩
    · rw [hT.embeddedImage_faces]
      exact ⟨s, hs, rfl⟩
    · change (insert 0 (s.image T)).image T.symm = insert c s
      simp only [Finset.image_insert, hKimage, hTi0]
  have hLfaces (s : Finset E) :
      s ∈ L.faces ↔ s.Nonempty ∧ (s.erase c = ∅ ∨ s.erase c ∈ K.faces) := by
    have hLiff : s ∈ L.faces ↔ s.image T ∈ C0.faces := by
      rw [hTi.embeddedImage_faces]
      constructor
      · rintro ⟨t, ht, hts⟩
        have hst : s.image T = t := by
          rw [← hts]
          ext x
          simp
        exact hst.symm ▸ ht
      · intro hs
        exact ⟨s.image T, hs, hKimage s⟩
    have hKiff (t : Finset E) : t.image T ∈ K0.faces ↔ t ∈ K.faces := by
      rw [hT.embeddedImage_faces]
      constructor
      · rintro ⟨u, hu, hut⟩
        have hut' : u = t := (hKimage u).symm.trans
          ((congrArg (fun r : Finset E => r.image T.symm) hut).trans (hKimage t))
        exact hut' ▸ hu
      · intro ht
        exact ⟨t, ht, rfl⟩
    rw [hLiff]
    change (s.image T).Nonempty ∧
      ((s.image T).erase 0 = ∅ ∨ (s.image T).erase 0 ∈ K0.faces) ↔ _
    rw [← hTc, ← Finset.image_erase T.injective s c,
      Finset.image_nonempty, Finset.image_eq_empty, hKiff]
  have hgPL : FinitePiecewiseAffineOn g S := hLS ▸ hg.finitePiecewiseAffineOn hL
  have hgc : g c = a := by change q (T c) = a; rw [hTc, hq0]
  have hgb : EqOn g b (frontier S) := by
    intro u hu
    have hTu : T u ∈ frontier S0 := hfront.subset (mem_image_of_mem T hu)
    change q (T u) = b u
    simpa using hqb hTu
  have hgW : MapsTo g S W := fun _ hx => hqW (mem_image_of_mem T hx)
  let j : S → S0 := fun x => ⟨T x, mem_image_of_mem T x.property⟩
  have hj : Continuous j := (T.continuous.comp continuous_subtype_val).subtype_mk _
  let H : C(I × S, W) :=
    H0.comp ⟨fun z => (z.1, j z.2), continuous_fst.prodMk (hj.comp continuous_snd)⟩
  refine ⟨L, g, H, hL, hLS, hKL, hLvertices, hcone, hLfaces, hg, hgPL, hgc,
    hgb, hgW, ?_, ?_, ?_, ?_⟩
  · intro u hu r hr
    have hTu : T u ∈ frontier S0 := hfront.subset (mem_image_of_mem T hu)
    have hcoord : T ((1 - r) • c + r • u) = r • T u := by
      change -c + ((1 - r) • c + r • u) = r • (-c + u)
      module
    change q (T ((1 - r) • c + r • u)) = _
    rw [hcoord, hqray (T u) hTu r hr]
    simp
  · intro x
    exact (hH00 (j x)).trans (by change f (T.symm (T x)) = f x; rw [T.symm_apply_apply])
  · intro x
    exact hH01 (j x)
  · intro t u
    have hju : j ⟨u, hS.isClosed.frontier_subset u.property⟩ =
        ⟨U u, hS0.isClosed.frontier_subset (U u).property⟩ := rfl
    change H0 (t, j ⟨u, hS.isClosed.frontier_subset u.property⟩) = B (t, u)
    rw [hju, hH0B]
    change B (t, U.symm (U u)) = B (t, u)
    rw [U.symm_apply_apply]



theorem AffineOnFaces.exists_boundary_cone_at_homotopy [Nontrivial E]
    {K : SimplicialComplex ℝ E} {b : E → F} (hb : K.AffineOnFaces b)
    (hK : K.faces.Finite) {S : Set E} (hS : IsCompact S) (hScv : Convex ℝ S)
    (c : E) (hc : c ∈ interior S) (hKS : K.space = frontier S)
    {W : Set F} (hW : Convex ℝ W) (f : E →ᴬ[ℝ] F) (hfW : MapsTo f S W)
    (B : C(I × frontier S, W))
    (hB0 : ∀ u : frontier S, (B (0, u) : F) = f u)
    (hB1 : ∀ u : frontier S, (B (1, u) : F) = b u)
    (a : F) (ha : a ∈ W) :
    ∃ (L : SimplicialComplex ℝ E) (g : E → F) (H : C(I × S, W)),
      L.faces.Finite ∧ L.space = S ∧ K ≤ L ∧ L.vertices = insert c K.vertices ∧
      (∀ s ∈ K.faces, insert c s ∈ L.faces) ∧
      L.AffineOnFaces g ∧ FinitePiecewiseAffineOn g S ∧ g c = a ∧
      EqOn g b (frontier S) ∧ MapsTo g S W ∧
      (∀ u ∈ frontier S, ∀ r ∈ Icc (0 : ℝ) 1,
        g ((1 - r) • c + r • u) = (1 - r) • a + r • b u) ∧
      (∀ x : S, (H (0, x) : F) = f x) ∧
      (∀ x : S, (H (1, x) : F) = g x) ∧
      ∀ (t : I) (u : frontier S),
        H (t, ⟨u, hS.isClosed.frontier_subset u.property⟩) = B (t, u) := by
  obtain ⟨L, g, H, hL, hLS, hKL, hLv, hcone, _, hg, hgPL, hgc, hgb,
    hgW, hgray, hH0, hH1, hHB⟩ :=
    hb.exists_boundary_cone_at_homotopy_with_faces hK hS hScv c hc hKS
      hW f hfW B hB0 hB1 a ha
  exact ⟨L, g, H, hL, hLS, hKL, hLv, hcone, hg, hgPL, hgc, hgb,
    hgW, hgray, hH0, hH1, hHB⟩

end Geometry.SimplicialComplex
