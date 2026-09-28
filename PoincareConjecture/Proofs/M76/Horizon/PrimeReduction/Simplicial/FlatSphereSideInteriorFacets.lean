import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryMarks
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem faceLink_ncard_eq_two_of_flat_side_off_vertex
    (K N P : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hPK : P ≤ K)
    {s : Finset E} (hs : s ∈ P.faces) (hsc : s.card = 3)
    {p : E} (hps : p ∈ s) (hpN : p ∈ N.vertices)
    {q : E} (hqs : q ∈ s) (hqN : q ∉ N.space)
    {f : E → (Fin 3 → ℝ)}
    (hf : (K.closedStar p).AffineOnFaces f)
    (hinj : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space))
    (hP : (P.closedStar p).space = (K.closedStar p).space ∩ {x | 0 ≤ f x 0})
    (hN : (N.closedStar p).space = (K.closedStar p).space ∩ {x | f x 0 = 0}) :
    (P.faceLink s).vertices.ncard = 2 := by
  classical
  have hstarle : P.closedStar p ≤ K.closedStar p := fun _ ht => ⟨hPK ht.1, hPK ht.2⟩
  have hstarsub := space_subset_of_le hstarle
  have hfP : (P.closedStar p).AffineOnFaces f := fun t ht => hf t (hstarle ht)
  have hinjP := hinj.mono hstarsub
  have hsstar : s ∈ (P.closedStar p).faces :=
    ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
  have hqstar := (P.closedStar p).subset_space hsstar hqs
  have hpNstar : p ∈ (N.closedStar p).space := by
    apply (N.closedStar p).vertices_subset_space
    refine ⟨hpN, ?_⟩
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
    exact hpN
  have hpzero : f p 0 = 0 := (hN.subset hpNstar).2
  have hqpos : 0 < f q 0 := by
    have hqnonneg := (hP.subset hqstar).2
    have hqne : f q 0 ≠ 0 := by
      intro he
      have hqNstar := hN.symm.subset ⟨hstarsub hqstar, he⟩
      exact hqN (space_subset_of_le (K := N.closedStar p) (L := N) (fun _ ht => ht.1) hqNstar)
    exact lt_of_le_of_ne hqnonneg (Ne.symm hqne)
  have himage : f '' (P.closedStar p).space =
      (f '' (K.closedStar p).space) ∩ {y | 0 ≤ y 0} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_image_of_mem f (hP.subset hx).1, (hP.subset hx).2⟩
    · rintro ⟨⟨x, hx, rfl⟩, hpos⟩
      exact ⟨x, hP.symm.subset ⟨hx, hpos⟩, rfl⟩
  have hpclosure : f p ∈ closure (openSegment ℝ (f p) (f q)) :=
    segment_subset_closure_openSegment (left_mem_segment ℝ (f p) (f q))
  obtain ⟨y, hyint, hyseg⟩ := mem_closure_iff.mp hpclosure
    (interior (f '' (K.closedStar p).space)) isOpen_interior hint
  have hypos : 0 < y 0 := by
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hyseg
    change 0 < a * f p 0 + b * f q 0
    rw [hpzero, mul_zero, zero_add]
    exact mul_pos hb hqpos
  have hyPint : y ∈ interior (f '' (P.closedStar p).space) := by
    apply interior_maximal (t := interior (f '' (K.closedStar p).space) ∩ {y | 0 < y 0})
      ?_ (isOpen_interior.inter (isOpen_lt continuous_const (continuous_apply 0))) ⟨hyint, hypos⟩
    intro z hz
    exact himage.symm.subset ⟨interior_subset hz.1, (show 0 < z 0 from hz.2).le⟩
  have hyhull : y ∈ convexHull ℝ (s.image f : Set (Fin 3 → ℝ)) :=
    (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩))
      (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨q, hqs, rfl⟩))
      (openSegment_subset_segment ℝ _ _ hyseg)
  let J := hfP.embeddedImage hinjP
  have hJ := hfP.embeddedImage_finite hinjP (finite_closedStar_faces (hK.subset hPK) p)
  have hsJ : s.image f ∈ J.faces :=
    (hfP.image_mem_embeddedImage_iff hinjP ((P.closedStar p).subset_space hsstar)).mpr hsstar
  have hscJ : (s.image f).card = Module.finrank ℝ (Fin 3 → ℝ) := by
    rw [Finset.card_image_iff.mpr (hinjP.mono ((P.closedStar p).subset_space hsstar)), hsc]
    simp
  have hyJ : y ∈ interior J.space := by
    rw [hfP.embeddedImage_space hinjP]
    exact hyPint
  have hcount := J.faceLink_ncard_eq_two_of_hull_meets_interior hJ hsJ hscJ ⟨y, hyhull, hyJ⟩
  rw [hfP.ncard_embeddedImage_faceLink hinjP hsstar] at hcount
  have hSl : (P.closedStar p).faceLink s = P.faceLink s := by
    rw [← P.closedFaceStar_singleton_eq_closedStar]
    exact P.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hSl] at hcount

theorem faceLink_ncard_eq_two_of_flat_side_unmarked
    (K N P : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hPK : P ≤ K) (hNP : N ≤ P)
    (hfull : ∀ a ∈ P.faces, (∀ v ∈ a, v ∈ N.vertices) → a ∈ N.faces)
    {s : Finset E} (hs : s ∈ P.faces) (hsc : s.card = 3) (hsN : s ∉ N.faces)
    {p : E} (hps : p ∈ s) (hpN : p ∈ N.vertices)
    {f : E → (Fin 3 → ℝ)}
    (hf : (K.closedStar p).AffineOnFaces f)
    (hinj : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space))
    (hP : (P.closedStar p).space = (K.closedStar p).space ∩ {x | 0 ≤ f x 0})
    (hN : (N.closedStar p).space = (K.closedStar p).space ∩ {x | f x 0 = 0}) :
    (P.faceLink s).vertices.ncard = 2 := by
  obtain ⟨q, hqs, hqN⟩ := exists_vertex_off_full_subcomplex hNP hfull hs hsN
  exact K.faceLink_ncard_eq_two_of_flat_side_off_vertex N P hK hPK
    hs hsc hps hpN hqs hqN hf hinj hint hP hN

end Geometry.SimplicialComplex
