import PoincareConjecture.Proofs.M76.Mathlib.RadialHeightCorrection
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedImageReparameterization
import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryCone
import PoincareConjecture.Proofs.M76.Mathlib.RelativeRadialHeightCorrection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronNeighborhoodRetraction













set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem IsFinitePL.exists_radial_height_corrected_frontier_relative
    {S P : Set E} {D : Set F} {H : S ≃ₜ frontier D} (hH : H.IsFinitePL)
    (hDcv : Convex ℝ D) (hDzero : (0 : F) ∈ interior D)
    (A : E →ₗ[ℝ] ℝ) (B C : F →ₗ[ℝ] ℝ)
    (hpos : ∀ x : S, 0 ≤ A x ↔ 0 ≤ B (H x))
    (hneg : ∀ x : S, A x ≤ 0 ↔ B (H x) ≤ 0)
    (hplane : ∀ x : S, (x : E) ∈ P ↔ C (H x) = 0)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite)
    (hJD : J.space ⊆ frontier D)
    (hJheight : ∀ y : frontier D, (y : F) ∈ J.space → A (H.symm y) = B y) :
    ∃ (K : SimplicialComplex ℝ E) (f : E → F)
      (hf : K.AffineOnFaces f) (hinj : InjOn f K.space),
      K.faces.Finite ∧ K.space = S ∧
      (∀ s ∈ (hf.embeddedImage hinj).faces, LinearIndependent ℝ ((↑) : s → F)) ∧
      InjOn (NormedSpace.normalize : F → F) (hf.embeddedImage hinj).space ∧
      NormedSpace.normalize '' (hf.embeddedImage hinj).space =
        NormedSpace.normalize '' frontier D ∧
      ∃ G : S ≃ₜ (hf.embeddedImage hinj).space, G.IsFinitePL ∧
        (∀ x : S, (G x : F) = f x) ∧
        (∀ x : S, B (G x) = A x) ∧
        (∀ x : S, C (G x) = 0 ↔ (x : E) ∈ P) ∧
        (∀ x : S, (H x : F) ∈ J.space → (G x : F) = H x) := by
  classical
  obtain ⟨g, ⟨T, hT, hTs, hgT⟩, hHg⟩ := hH.symm
  let N := hT.toFinset.sup Finset.card
  have hN (s : Finset F) (hs : s ∈ T.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hT.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨U, hU, hUT, _, hUC⟩ :=
    T.exists_subdivision_respectsAffineHyperplane hT hN C.toAffineMap
  have hUs : U.space = frontier D := hUT.space_eq.trans hTs
  obtain ⟨L, M, hL, hLU, hML, hMs⟩ :=
    U.exists_subdivision_with_polyhedron_subcomplex J hU hJ (hJD.trans hUs.symm.subset)
  have hLT := hLU.trans hUT
  have hLC := hLU.respectsAffineHyperplane hUC
  have hLs : L.space = frontier D := hLT.space_eq.trans hTs
  have hg : L.AffineOnFaces g := hgT.of_face_containment hLT.face_subset
  have hgval (y : L.space) : (H.symm ⟨y, hLs ▸ y.property⟩ : E) = g y :=
    hHg ⟨y, hLs ▸ y.property⟩
  have hinjg : InjOn g L.space := by
    intro x hx y hy hxy
    have heq : H.symm ⟨x, hLs ▸ hx⟩ = H.symm ⟨y, hLs ▸ hy⟩ := by
      apply Subtype.ext
      simpa only [hHg] using hxy
    exact congrArg Subtype.val (H.symm.injective heq)
  have hlin := L.linearIndependent_faces_of_space_subset_frontier hDcv hDzero hLs.subset
  have hrad : InjOn (NormedSpace.normalize : F → F) L.space :=
    (hDcv.injOn_normalize_frontier hDzero).mono hLs.subset
  have hscalar : L.AffineOnFaces (A ∘ g) :=
    hg.postcomp A.toContinuousLinearMap.toContinuousAffineMap
  have hscalarNeg (x : F) (hx : x ∈ L.vertices) : (A ∘ g) x < 0 ↔ B x < 0 := by
    let y : frontier D := ⟨x, hLs ▸ L.vertices_subset_space hx⟩
    have h := not_congr (hpos (H.symm y))
    simpa only [not_le, H.apply_symm_apply, hHg, Function.comp_apply] using h
  have hscalarPos (x : F) (hx : x ∈ L.vertices) : 0 < (A ∘ g) x ↔ 0 < B x := by
    let y : frontier D := ⟨x, hLs ▸ L.vertices_subset_space hx⟩
    have h := not_congr (hneg (H.symm y))
    simpa only [not_le, H.apply_symm_apply, hHg, Function.comp_apply] using h
  have hscalarM : EqOn (A ∘ g) B M.vertices := by
    intro x hx
    let y : frontier D := ⟨x, hJD (hMs ▸ M.vertices_subset_space hx)⟩
    have h := hJheight y (hMs ▸ M.vertices_subset_space hx)
    simpa only [hHg, Function.comp_apply] using h
  obtain ⟨r, hr, v, e, hv, hev, hvvertex, _, hheight, hzero, hfix⟩ :=
    L.exists_radial_height_correction_fixed_subcomplex M hML hL hlin hrad
      (A ∘ g) hscalar B C hLC hscalarNeg hscalarPos hscalarM
  let R := L.radialRescale hlin hrad r hr
  have hinjv : InjOn v L.space := by
    intro x hx y hy hxy
    have heq : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hev] using hxy
    exact congrArg Subtype.val (e.injective heq)
  have hRv : hv.embeddedImage hinjv = R := by
    have hface (s : Finset F) (hs : s ∈ L.faces) :
        s.image v = s.image (fun x => r x • x) := by
      apply Finset.image_congr
      exact fun x hx => hvvertex (L.face_subset_vertices hs hx)
    ext s
    rw [hv.embeddedImage_faces hinjv, L.radialRescale_faces hlin hrad r hr]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, (hface t ht).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, hface t ht⟩
  let K := hg.embeddedImage hinjg
  have hK : K.faces.Finite := hg.embeddedImage_finite hinjg hL
  have hKs : K.space = S := by
    rw [hg.embeddedImage_space hinjg, hLs]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← hHg ⟨y, hy⟩]
      exact (H.symm ⟨y, hy⟩).property
    · intro hx
      refine ⟨H ⟨x, hx⟩, (H ⟨x, hx⟩).property, ?_⟩
      rw [← hHg, H.symm_apply_apply]
  let u := Function.invFunOn g L.space
  have hleft : LeftInvOn u g L.space := hinjg.leftInvOn_invFunOn
  let f := v ∘ u
  have hf : K.AffineOnFaces f := hg.comp_inverse_on_embeddedImage hv hinjg hleft
  have hinj : InjOn f K.space := hg.injOn_comp_inverse_on_embeddedImage hinjg hinjv hleft
  have hImage : hf.embeddedImage hinj = R :=
    (hg.embeddedImage_comp_inverse hv hinjg hinjv hleft hf hinj).trans hRv
  let eg := hg.embeddedHomeomorph hinjg hL
  let G := (Homeomorph.setCongr hKs.symm).trans
    (eg.symm.trans (e.trans (Homeomorph.setCongr (congrArg SimplicialComplex.space hImage).symm)))
  have hG (x : S) : (G x : F) = f x := by
    let z : K.space := ⟨x, hKs.symm ▸ x.property⟩
    change (e (eg.symm z) : F) = v (u x)
    rw [hev, hg.embeddedHomeomorph_symm_apply hinjg hL]
  refine ⟨K, f, hf, hinj, hK, hKs, ?_, ?_, ?_, G,
    ⟨f, ⟨K, hK, hKs, hf⟩, hG⟩, hG, ?_, ?_, ?_⟩
  · rw [hImage]
    exact fun _ hs => L.linearIndependent_radialRescale_face hlin hrad r hr hs
  · rw [hImage]
    exact L.injOn_normalize_radialRescale hlin hrad r hr
  · rw [hImage, L.normalize_image_radialRescale_space hlin hrad r hr, hLs]
  · intro x
    let z : K.space := ⟨x, hKs.symm ▸ x.property⟩
    have hgy : g (eg.symm z) = (x : E) :=
      congrArg Subtype.val (eg.apply_symm_apply z)
    change B (e (eg.symm z)) = A x
    rw [hheight]
    exact congrArg A hgy
  · intro x
    let z : K.space := ⟨x, hKs.symm ▸ x.property⟩
    let y := eg.symm z
    have hgy : g y = (x : E) := congrArg Subtype.val (eg.apply_symm_apply z)
    have hpre : H.symm ⟨y, hLs ▸ y.property⟩ = x :=
      Subtype.ext ((hgval y).trans hgy)
    have hy : (y : F) = (H x : F) := by
      have heq := congrArg H hpre
      rw [H.apply_symm_apply] at heq
      exact congrArg Subtype.val heq
    change C (e y) = 0 ↔ (x : E) ∈ P
    rw [hzero, hy]
    exact (hplane x).symm
  · intro x hx
    let z : K.space := ⟨x, hKs.symm ▸ x.property⟩
    let y := eg.symm z
    have hgy : g y = (x : E) := congrArg Subtype.val (eg.apply_symm_apply z)
    have hpre : H.symm ⟨y, hLs ▸ y.property⟩ = x :=
      Subtype.ext ((hgval y).trans hgy)
    have hy : (y : F) = (H x : F) := by
      have heq := congrArg H hpre
      rw [H.apply_symm_apply] at heq
      exact congrArg Subtype.val heq
    have hyJ : (y : F) ∈ J.space := hy.symm ▸ hx
    have hyM : (y : F) ∈ M.space := hMs.symm ▸ hyJ
    change (e y : F) = (H x : F)
    exact (hev y).trans ((hfix hyM).trans hy)







theorem IsFinitePL.exists_radial_height_corrected_frontier
    {S P : Set E} {D : Set F} {H : S ≃ₜ frontier D} (hH : H.IsFinitePL)
    (hDcv : Convex ℝ D) (hDzero : (0 : F) ∈ interior D)
    (A : E →ₗ[ℝ] ℝ) (B C : F →ₗ[ℝ] ℝ)
    (hpos : ∀ x : S, 0 ≤ A x ↔ 0 ≤ B (H x))
    (hneg : ∀ x : S, A x ≤ 0 ↔ B (H x) ≤ 0)
    (hplane : ∀ x : S, (x : E) ∈ P ↔ C (H x) = 0) :
    ∃ (K : SimplicialComplex ℝ E) (f : E → F)
      (hf : K.AffineOnFaces f) (hinj : InjOn f K.space),
      K.faces.Finite ∧ K.space = S ∧
      (∀ s ∈ (hf.embeddedImage hinj).faces, LinearIndependent ℝ ((↑) : s → F)) ∧
      InjOn (NormedSpace.normalize : F → F) (hf.embeddedImage hinj).space ∧
      NormedSpace.normalize '' (hf.embeddedImage hinj).space =
        NormedSpace.normalize '' frontier D ∧
      ∃ G : S ≃ₜ (hf.embeddedImage hinj).space, G.IsFinitePL ∧
        (∀ x : S, (G x : F) = f x) ∧
        (∀ x : S, B (G x) = A x) ∧
        (∀ x : S, C (G x) = 0 ↔ (x : E) ∈ P) := by
  obtain ⟨K, f, hf, hinj, hK, hKs, hlin, hrad, himage, G, hG, hGf, hheight,
      hzero, _⟩ := hH.exists_radial_height_corrected_frontier_relative hDcv hDzero
    A B C hpos hneg hplane ⊥ Set.finite_empty
    (by simp only [SimplicialComplex.space_bot, empty_subset])
    (by
      intro y hy
      simp only [SimplicialComplex.space_bot, mem_empty_iff_false] at hy)
  exact ⟨K, f, hf, hinj, hK, hKs, hlin, hrad, himage, G, hG, hGf, hheight, hzero⟩

end Homeomorph
