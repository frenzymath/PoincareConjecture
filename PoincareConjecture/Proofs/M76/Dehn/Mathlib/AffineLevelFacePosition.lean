import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineFacePosition










set_option autoImplicit false

open Set

namespace Geometry




theorem affine_level_span_eq_or_disjoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : AffineSubspace ℝ E) (l : List E) (f : E → E) (T : Set E)
    (havoid : ∀ (p : List E) (v : E) (q : List E), l = p ++ v :: q →
      ∀ S : Finset E, (S : Set E) ⊆ T ∪ f '' {w | w ∈ p} →
        ¬A ≤ affineSpan ℝ (S : Set E) → f v ∉ affineSpan ℝ (S : Set E))
    (s t : Finset E) (hfree : ∃ v ∈ l, v ∈ s)
    (hfixed : ∀ w ∈ s, w ∉ l → f w ∈ T)
    (ht : (t : Set E) ⊆ T)
    (hsA : ∀ w ∈ s, f w ∈ A) (htA : ∀ w ∈ t, w ∈ A) :
    affineSpan ℝ (f '' (s : Set E) ∪ (t : Set E)) = A ∨
      Disjoint (intrinsicInterior ℝ (convexHull ℝ (f '' (s : Set E))))
        (convexHull ℝ (t : Set E)) := by
  classical
  obtain ⟨p, v, q, he, hv, hq⟩ := l.exists_split_last_mem_set (s : Set E) hfree
  let S : Finset E := (s.erase v).image f ∪ t
  have hSfull : (S : Set E) ⊆ f '' (s : Set E) ∪ (t : Set E) := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      exact Or.inl (mem_image_of_mem f (Finset.mem_erase.mp hw).2)
    · exact Or.inr hy
  by_cases htop : A ≤ affineSpan ℝ (S : Set E)
  · left
    apply le_antisymm
    · apply affineSpan_le.mpr
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩ | hz
      · exact hsA z hz
      · exact htA y hz
    · exact htop.trans (affineSpan_mono ℝ hSfull)
  · right
    have hST : (S : Set E) ⊆ T ∪ f '' {w | w ∈ p} := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
        have hwv := Finset.mem_erase.mp hw
        by_cases hwl : w ∈ l
        · have hwp : w ∈ p := by
            rw [he] at hwl
            rcases List.mem_append.mp hwl with hp | hq'
            · exact hp
            · rcases List.mem_cons.mp hq' with hewv | hwq
              · exact (hwv.1 hewv).elim
              · exact (hq w hwq hwv.2).elim
          exact Or.inr ⟨w, hwp, rfl⟩
        · exact Or.inl (hfixed w hwv.2 hwl)
      · exact Or.inl (ht hy)
    have hexcluded := havoid p v q he S hST htop
    apply AffineSubspace.disjoint_intrinsicInterior_convexHulls_of_excluded_vertex
      (mem_image_of_mem f hv)
    intro hmem
    apply hexcluded
    apply affineSpan_mono ℝ ?_ hmem
    rintro y (⟨⟨w, hw, rfl⟩, hne⟩ | hy)
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      refine ⟨w, Finset.mem_erase.mpr ⟨?_, hw⟩, rfl⟩
      intro hewv
      exact hne (congrArg f hewv)
    · exact Finset.mem_union.mpr (Or.inr hy)

end Geometry
