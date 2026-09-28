import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarProjectionCoverage

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_full_face_of_mem_closure_interior (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {x : E} (hx : x ∈ closure (interior K.space)) :
    ∃ s ∈ K.faces, s.card = Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (s : Set E) := by
  classical
  let S : Set (Finset E) :=
    {s | s ∈ K.faces ∧ affineSpan ℝ (s : Set E) ≠ ⊤}
  have hS : S.Finite := hK.subset (fun _ hs => hs.1)
  let : Finite S := hS.to_subtype
  let A : S → AffineSubspace ℝ E := fun s => affineSpan ℝ (s.val : Set E)
  have hproper : ∀ s, A s ≠ ⊤ := fun s => s.property.2
  let T : Set (Finset E) :=
    {s | s ∈ K.faces ∧ affineSpan ℝ (s : Set E) = ⊤}
  have hT : T.Finite := hK.subset (fun _ hs => hs.1)
  let P : Set E := ⋃ s ∈ T, convexHull ℝ (s : Set E)
  have hP : IsClosed P :=
    (hT.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have havoid : interior K.space \ ⋃ s, (A s : Set E) ⊆ P := by
    intro y hy
    obtain ⟨s, hs, hys⟩ := mem_space_iff.mp (interior_subset hy.1)
    have hspan : affineSpan ℝ (s : Set E) = ⊤ := by
      by_contra hnot
      exact hy.2 (mem_iUnion.mpr
        ⟨⟨s, hs, hnot⟩, convexHull_subset_affineSpan _ hys⟩)
    exact mem_iUnion₂.mpr ⟨s, ⟨hs, hspan⟩, hys⟩
  have hclosure : interior K.space ⊆
      closure (interior K.space \ ⋃ s, (A s : Set E)) := by
    simpa only [sdiff_eq_compl_inter, inter_comm] using
      (AffineSubspace.dense_compl_iUnion A hproper).open_subset_closure_inter
        isOpen_interior
  have hintP : interior K.space ⊆ P := hclosure.trans (closure_minimal havoid hP)
  have hxP : x ∈ P := closure_minimal hintP hP hx
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hxP
  refine ⟨s, hs.1, ?_, hxs⟩
  have hrange : range ((↑) : s → E) = (s : Set E) := by ext y; simp
  have hspan : affineSpan ℝ (range ((↑) : s → E)) = ⊤ := by
    rw [hrange]
    exact hs.2
  simpa using (K.indep hs.1).affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hspan

theorem exists_full_face_of_mem_interior (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {x : E} (hx : x ∈ interior K.space) :
    ∃ s ∈ K.faces, s.card = Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (s : Set E) :=
  K.exists_full_face_of_mem_closure_interior hK (subset_closure hx)

theorem exists_full_face_of_mem_convex_space (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hcv : Convex ℝ K.space)
    (hne : (interior K.space).Nonempty) {x : E} (hx : x ∈ K.space) :
    ∃ s ∈ K.faces, s.card = Module.finrank ℝ E + 1 ∧
      x ∈ convexHull ℝ (s : Set E) := by
  have hspace : closure (interior K.space) = K.space := by
    rw [hcv.closure_interior_eq_closure_of_nonempty_interior hne,
      (K.isCompact_space_of_finite hK).isClosed.closure_eq]
  exact K.exists_full_face_of_mem_closure_interior hK (hspace.symm ▸ hx)

theorem exists_full_coface_of_convex_space (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hcv : Convex ℝ K.space)
    (hne : (interior K.space).Nonempty) {s : Finset E} (hs : s ∈ K.faces) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = Module.finrank ℝ E + 1 := by
  have hsne : (convexHull ℝ (s : Set E)).Nonempty :=
    (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ _) hsne
  obtain ⟨t, ht, htcard, hxt⟩ := K.exists_full_face_of_mem_convex_space hK hcv hne
    (K.convexHull_subset_space hs (intrinsicInterior_subset hx))
  exact ⟨t, ht, K.subset_of_mem_intrinsicInterior_face hs ht hx hxt, htcard⟩

end Geometry.SimplicialComplex
