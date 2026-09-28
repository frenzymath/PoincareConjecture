import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.PrescribedSubdivisionVertices











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem FinitePiecewiseAffineOn.exists_interval_image_graph
    {f : ℝ → E} (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1))
    (P : Finset E) (hP : (P : Set E) ⊆ f '' Icc (0 : ℝ) 1) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧
      K.space = f '' Icc (0 : ℝ) 1 ∧
      (∀ s ∈ K.faces, s.card ≤ 2) ∧ (P : Set E) ⊆ K.vertices := by
  classical
  obtain ⟨L, hL, hLI, hfL⟩ := hf
  have hdim (s : Finset ℝ) (hs : s ∈ L.faces) : s.card ≤ 2 := by
    have h := (L.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa only [Fintype.card_coe, Module.finrank_self, Nat.reduceAdd] using h
  obtain ⟨J, hJ, hJs, hfaces⟩ := hfL.exists_finite_triangulation_image hL
  have himage : J.space = f '' Icc (0 : ℝ) 1 := hJs.trans (congrArg (f '' ·) hLI)
  have hJdim (s : Finset E) (hs : s ∈ J.faces) : s.card ≤ 2 := by
    obtain ⟨t, ht, _, hcard⟩ := hfaces s hs
    exact hcard.trans (hdim t ht)
  obtain ⟨K, hK, hKJ, hPK⟩ := J.exists_finite_subdivision_with_vertices hJ P
    (fun x hx => himage.symm ▸ hP hx)
  refine ⟨K, hK, hKJ.space_eq.trans himage, ?_, hPK⟩
  intro s hs
  obtain ⟨t, ht, hst⟩ := hKJ.face_subset s hs
  have hspan : (s : Set E) ⊆ affineSpan ℝ (t : Set E) :=
    (subset_convexHull ℝ _).trans (hst.trans (convexHull_subset_affineSpan _))
  exact ((K.indep hs).card_le_card_of_subset_affineSpan hspan).trans (hJdim t ht)

end Geometry
