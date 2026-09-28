import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs

set_option autoImplicit false
open Set Geometry

namespace Set

theorem IsFinitePLBallPair.exists_finite_interval_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d r : Set E} (hd : IsFinitePLBallPair ℝ d r) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = d ∧
      ∀ s ∈ K.faces, s.card ≤ 2 := by
  classical
  obtain ⟨_, C, _, _, _, e, he, _⟩ := hd
  obtain ⟨f, ⟨J, hJ, hJs, hf⟩, hef⟩ := he.symm
  have himage : f '' C = d := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e.symm ⟨x, hx⟩).property
    · intro x hx
      exact ⟨e ⟨x, hx⟩, (e ⟨x, hx⟩).property, by rw [← hef, e.symm_apply_apply]⟩
  obtain ⟨K, hK, hKs, hfaces⟩ := hf.exists_finite_triangulation_image hJ
  refine ⟨K, hK, hKs.trans (hJs ▸ himage), ?_⟩
  intro s hs
  obtain ⟨t, ht, _, hst⟩ := hfaces s hs
  have hdim := (J.indep ht).card_le_finrank_succ.trans
    (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  exact hst.trans (by simpa using hdim)

theorem exists_finite_interval_union_complex
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (d r : ι → Set E) (hd : ∀ i, IsFinitePLBallPair ℝ (d i) (r i)) :
    ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = ⋃ i, d i ∧
      (∀ s ∈ K.faces, s.card ≤ 2) ∧
      ∀ s ∈ K.faces, ∃ i, convexHull ℝ (s : Set E) ⊆ d i := by
  classical
  choose J hJ hJs hJdim using fun i => (hd i).exists_finite_interval_complex
  obtain ⟨K, hK, hKs, hfaces⟩ := SimplicialComplex.exists_finite_triangulation_iUnion J hJ
  refine ⟨K, hK, by simpa only [hJs] using hKs, ?_, ?_⟩
  · intro s hs
    obtain ⟨i, t, ht, hst⟩ := hfaces s hs
    have hspan : (s : Set E) ⊆ affineSpan ℝ (t : Set E) :=
      (subset_convexHull ℝ _).trans (hst.trans (convexHull_subset_affineSpan _))
    exact ((K.indep hs).card_le_card_of_subset_affineSpan hspan).trans (hJdim i t ht)
  · intro s hs
    obtain ⟨i, t, ht, hst⟩ := hfaces s hs
    exact ⟨i, hst.trans ((J i).convexHull_subset_space ht) |>.trans (hJs i).subset⟩

end Set
