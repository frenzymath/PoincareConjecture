import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteSubcomplexContact

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

theorem original_arc_model_contacts
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L C : Set X} (hL : IsClosed L) (hLC : L ⊆ C)
    {q : ℝ → X}
    (hzero : q 0 ∈ frontier L) (hone : q 1 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L)
    (hqC : MapsTo q (Icc (0 : ℝ) 1) C)
    {F : X → E} (hF : InjOn F C)
    (K A P D : SimplicialComplex ℝ E) (hAK : A ≤ K) (hDK : D ≤ K)
    (hA : A.space = F '' (q '' Icc (0 : ℝ) 1))
    (hP : P.space = F '' L) (hD : D.space = F '' frontier L) :
    A.space ∩ P.space = {F (q 0), F (q 1)} ∧
    A.space ∩ D.space = {F (q 0), F (q 1)} ∧
    F (q 0) ∈ A.vertices ∧ F (q 0) ∈ D.vertices ∧
    F (q 1) ∈ A.vertices ∧ F (q 1) ∈ D.vertices := by
  classical
  have hqL : q '' Icc (0 : ℝ) 1 ∩ L = {q 0, q 1} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, htL⟩
      by_cases ht0 : t = 0
      · subst t
        exact mem_insert _ _
      by_cases ht1 : t = 1
      · subst t
        exact mem_insert_of_mem _ (mem_singleton _)
      exact False.elim (hproper t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
        lt_of_le_of_ne ht.2 ht1⟩ htL)
    · intro hx
      rcases mem_insert_iff.mp hx with rfl | hx
      · exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, hL.frontier_subset hzero⟩
      · rcases mem_singleton_iff.mp hx with rfl
        exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, hL.frontier_subset hone⟩
  have hqD : q '' Icc (0 : ℝ) 1 ∩ frontier L = {q 0, q 1} := by
    apply Subset.antisymm
    · exact (inter_subset_inter_right _ hL.frontier_subset).trans hqL.subset
    · intro x hx
      rcases mem_insert_iff.mp hx with rfl | hx
      · exact ⟨⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, hzero⟩
      · rcases mem_singleton_iff.mp hx with rfl
        exact ⟨⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, hone⟩
  have hqsub : q '' Icc (0 : ℝ) 1 ⊆ C := image_subset_iff.mpr hqC
  have hAP : A.space ∩ P.space = {F (q 0), F (q 1)} := by
    rw [hA, hP, ← hF.image_inter hqsub hLC, hqL, image_pair]
  have hAD : A.space ∩ D.space = {F (q 0), F (q 1)} := by
    rw [hA, hD, ← hF.image_inter hqsub (hL.frontier_subset.trans hLC), hqD, image_pair]
  have hfinite : (A.space ∩ D.space).Finite := by
    rw [hAD]
    exact (finite_singleton _).insert _
  have h0 : F (q 0) ∈ A.space ∩ D.space := hAD.symm.subset (mem_insert _ _)
  have h1 : F (q 1) ∈ A.space ∩ D.space :=
    hAD.symm.subset (mem_insert_of_mem _ (mem_singleton _))
  have hv0 := mem_vertices_of_finite_subcomplex_intersection hAK hDK hfinite h0.1 h0.2
  have hv1 := mem_vertices_of_finite_subcomplex_intersection hAK hDK hfinite h1.1 h1.2
  exact ⟨hAP, hAD, hv0.1, hv0.2, hv1.1, hv1.2⟩

end PoincareConjecture.M76
