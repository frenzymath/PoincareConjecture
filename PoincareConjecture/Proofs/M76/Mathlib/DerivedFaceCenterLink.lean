import PoincareConjecture.Proofs.M76.Mathlib.DerivedFaceChainIncidence
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph










set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)




theorem derived_faceCenter_link_vertices (s : K.faces) :
    ((K.derivedSubdivision c hc).link (c s)).vertices =
      c '' {t : K.faces | t ≠ s ∧ (t ≤ s ∨ s ≤ t)} := by
  classical
  have hcinj := K.positiveFaceCenter_injective c hc
  ext x
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := (K.derivedSubdivision_vertices_eq_range c hc).subset hx.1
    have hts : t ≠ s := by
      intro h
      exact hx.2.1 (Finset.mem_singleton.mpr (congrArg c h.symm))
    have hface : ({s, t} : Finset K.faces).image c ∈ (K.derivedSubdivision c hc).faces := by
      simpa only [Finset.image_insert, Finset.image_singleton] using hx.2.2
    have hchain := (K.image_mem_derivedSubdivision_faces_iff c hc _).mp hface |>.2
    exact ⟨t, ⟨hts, hchain t (by simp) s (by simp)⟩, rfl⟩
  · rintro ⟨t, ⟨hts, hcomp⟩, rfl⟩
    refine ⟨(K.derivedSubdivision_vertices_eq_range c hc).superset ⟨t, rfl⟩, ?_, ?_⟩
    · intro h
      exact hts (hcinj (Finset.mem_singleton.mp h)).symm
    · have hface : ({s, t} : Finset K.faces).image c ∈ (K.derivedSubdivision c hc).faces := by
        apply (K.image_mem_derivedSubdivision_faces_iff c hc _).mpr
        refine ⟨Finset.insert_nonempty _ _, ?_⟩
        intro i hi j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · exact Or.inl le_rfl
        · exact hcomp.symm
        · exact hcomp
        · exact Or.inl le_rfl
      simpa only [Finset.image_insert, Finset.image_singleton] using hface





theorem pair_mem_derived_faceCenter_link_of_comparable
    (s t u : K.faces) (ht : t ≠ s) (hu : u ≠ s)
    (hts : t ≤ s ∨ s ≤ t) (hus : u ≤ s ∨ s ≤ u) (htu : t ≤ u ∨ u ≤ t) :
    {c t, c u} ∈ ((K.derivedSubdivision c hc).link (c s)).faces := by
  classical
  have hcinj := K.positiveFaceCenter_injective c hc
  refine ⟨?_, ?_, ?_⟩
  · have hface : ({t, u} : Finset K.faces).image c ∈ (K.derivedSubdivision c hc).faces := by
      apply (K.image_mem_derivedSubdivision_faces_iff c hc _).mpr
      refine ⟨Finset.insert_nonempty _ _, ?_⟩
      intro i hi j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact Or.inl le_rfl
      · exact htu
      · exact htu.symm
      · exact Or.inl le_rfl
    simpa only [Finset.image_insert, Finset.image_singleton] using hface
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact ht (hcinj h).symm
    · exact hu (hcinj (Finset.mem_singleton.mp h)).symm
  · have hface : ({s, t, u} : Finset K.faces).image c ∈ (K.derivedSubdivision c hc).faces := by
      apply (K.image_mem_derivedSubdivision_faces_iff c hc _).mpr
      refine ⟨Finset.insert_nonempty _ _, ?_⟩
      intro i hi j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
      · exact Or.inl le_rfl
      · exact hts.symm
      · exact hus.symm
      · exact hts
      · exact Or.inl le_rfl
      · exact htu
      · exact hus
      · exact htu.symm
      · exact Or.inl le_rfl
    simpa only [Finset.image_insert, Finset.image_singleton] using hface





theorem connected_derived_faceCenter_link_of_strict_faces
    (r s u : K.faces) (hrs : r < s) (hsu : s < u) :
    ((K.derivedSubdivision c hc).link (c s)).vertexAbstractComplex.edgeGraph.Connected := by
  classical
  let D := (K.derivedSubdivision c hc).link (c s)
  have hvertex (t : K.faces) (ht : t ≠ s) (hcomp : t ≤ s ∨ s ≤ t) : c t ∈ D.vertices :=
    (K.derived_faceCenter_link_vertices c hc s).superset ⟨t, ⟨ht, hcomp⟩, rfl⟩
  let vr : D.vertices := ⟨c r, hvertex r hrs.ne (Or.inl hrs.le)⟩
  let vu : D.vertices := ⟨c u, hvertex u hsu.ne' (Or.inr hsu.le)⟩
  have hru : D.vertexAbstractComplex.edgeGraph.Reachable vr vu := by
    apply D.reachable_vertices_of_mem_face
      (K.pair_mem_derived_faceCenter_link_of_comparable c hc s r u hrs.ne hsu.ne'
        (Or.inl hrs.le) (Or.inr hsu.le) (Or.inl (hrs.le.trans hsu.le)))
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hreach (x : D.vertices) : D.vertexAbstractComplex.edgeGraph.Reachable x vu := by
    obtain ⟨t, ⟨ht, hcomp⟩, htx⟩ :=
      (K.derived_faceCenter_link_vertices c hc s).subset x.property
    rcases hcomp with hts | hst
    · apply D.reachable_vertices_of_mem_face
        (K.pair_mem_derived_faceCenter_link_of_comparable c hc s t u ht hsu.ne'
          (Or.inl hts) (Or.inr hsu.le) (Or.inl (hts.trans hsu.le)))
      · rw [← htx]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · apply SimpleGraph.Reachable.trans ?_ hru
      apply D.reachable_vertices_of_mem_face
        (K.pair_mem_derived_faceCenter_link_of_comparable c hc s t r ht hrs.ne
          (Or.inr hst) (Or.inl hrs.le) (Or.inr (hrs.le.trans hst)))
      · rw [← htx]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  let : Nonempty D.vertices := ⟨vr⟩
  exact ⟨fun x y => (hreach x).trans (hreach y).symm⟩

end Geometry.SimplicialComplex
