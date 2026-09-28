import PoincareConjecture.Proofs.M76.Mathlib.SimplicialCompatibleUnion

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {K E ι : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E]

theorem cross_inter_subset_of_common_subcomplex (C D J : SimplicialComplex K E)
    (hJC : J ≤ C) (hJD : J ≤ D) (hinter : C.space ∩ D.space ⊆ J.space)
    {s t : Finset E} (hs : s ∈ C.faces) (ht : t ∈ D.faces) :
    convexHull K (s : Set E) ∩ convexHull K (t : Set E) ⊆
      convexHull K ((s : Set E) ∩ t) := by
  classical
  rintro x ⟨hxs, hxt⟩
  obtain ⟨j, hj, hxj⟩ := mem_space_iff.mp
    (hinter ⟨C.convexHull_subset_space hs hxs, D.convexHull_subset_space ht hxt⟩)
  have hsj := C.inter_subset_convexHull hs (hJC hj) ⟨hxs, hxj⟩
  have htj := D.inter_subset_convexHull ht (hJD hj) ⟨hxt, hxj⟩
  have heq := (J.indep hj).convexHull_inter
    (t₁ := s ∩ j) (t₂ := t ∩ j) Finset.inter_subset_right Finset.inter_subset_right
  simp only [Finset.coe_inter] at heq
  have hx : x ∈ convexHull K (((s : Set E) ∩ j) ∩ ((t : Set E) ∩ j)) := by
    rw [heq]
    exact ⟨hsj, htj⟩
  have hsub : (((s : Set E) ∩ j) ∩ ((t : Set E) ∩ j)) ⊆ (s : Set E) ∩ t :=
    fun _ h => ⟨h.1.1, h.2.1⟩
  exact convexHull_mono hsub hx

omit [IsStrictOrderedRing K]

def iUnionOfCompatible (C : ι → SimplicialComplex K E)
    (hcross : ∀ i j, ∀ s ∈ (C i).faces, ∀ t ∈ (C j).faces,
      convexHull K (s : Set E) ∩ convexHull K (t : Set E) ⊆
        convexHull K ((s : Set E) ∩ t)) : SimplicialComplex K E where
  faces := ⋃ i, (C i).faces
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact ⟨(C i).nonempty_of_mem_faces hi,
      fun t hts ht => mem_iUnion.mpr ⟨i, (C i).down_closed hi hts ht⟩⟩
  indep := by
    intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact (C i).indep hi
  inter_subset_convexHull := by
    intro s t hs ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    obtain ⟨j, hj⟩ := mem_iUnion.mp ht
    exact hcross i j s hi t hj

variable (C : ι → SimplicialComplex K E)
  (hcross : ∀ i j, ∀ s ∈ (C i).faces, ∀ t ∈ (C j).faces,
    convexHull K (s : Set E) ∩ convexHull K (t : Set E) ⊆
      convexHull K ((s : Set E) ∩ t))

theorem faces_iUnionOfCompatible :
    (iUnionOfCompatible C hcross).faces = ⋃ i, (C i).faces := rfl

theorem le_iUnionOfCompatible (i : ι) : C i ≤ iUnionOfCompatible C hcross := by
  intro s hs
  exact mem_iUnion.mpr ⟨i, hs⟩

theorem space_iUnionOfCompatible :
    (iUnionOfCompatible C hcross).space = ⋃ i, (C i).space := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact mem_iUnion.mpr ⟨i, mem_space_iff.mpr ⟨s, hi, hxs⟩⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hi
    exact mem_space_iff.mpr ⟨s, mem_iUnion.mpr ⟨i, hs⟩, hxs⟩

theorem vertices_iUnionOfCompatible :
    (iUnionOfCompatible C hcross).vertices = ⋃ i, (C i).vertices := by
  ext x
  change ({x} ∈ ⋃ i, (C i).faces) ↔ x ∈ ⋃ i, (C i).vertices
  simp only [mem_iUnion]
  rfl

theorem finite_faces_iUnionOfCompatible [Finite ι] (hC : ∀ i, (C i).faces.Finite) :
    (iUnionOfCompatible C hcross).faces.Finite := finite_iUnion hC

end Geometry.SimplicialComplex
