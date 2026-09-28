import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralRefinement
import PoincareConjecture.Proofs.M76.Mathlib.AlignedHalfspaceFaces










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_finite_triangulation_iUnion_convexHull {ι : Type*} [Finite ι]
    (T : ι → Finset E) (hT : ∀ i, AffineIndependent ℝ ((↑) : T i → E)) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧
      L.space = ⋃ i, convexHull ℝ (T i : Set E) ∧
      ∀ s ∈ L.faces, ∃ i, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (T i : Set E) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hcompact : IsCompact (⋃ i, convexHull ℝ (T i : Set E)) :=
    isCompact_iUnion fun i => (T i).finite_toSet.isCompact_convexHull ℝ
  obtain ⟨K, hK, hUK, _⟩ := exists_finite_neighborhood_subset_normed
    hcompact isOpen_univ (subset_univ _)
  choose H hH using fun i => (T i).exists_affine_halfspaces_convexHull (hT i)
  let Htotal := Finset.univ.biUnion H
  let N := hK.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨R, hR, hRK, _, hRH⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hK hN Htotal
  let L : SimplicialComplex ℝ E := {
    faces := {s | s ∈ R.faces ∧
      ∃ i, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (T i : Set E)}
    indep := fun hs => R.indep hs.1
    isRelLowerSet_faces := by
      intro s hs
      refine ⟨R.nonempty_of_mem_faces hs.1, ?_⟩
      intro t hts ht
      obtain ⟨i, hi⟩ := hs.2
      exact ⟨R.down_closed hs.1 hts ht, i, (convexHull_mono hts).trans hi⟩
    inter_subset_convexHull := fun hs ht => R.inter_subset_convexHull hs.1 ht.1 }
  refine ⟨L, hR.subset (fun _ hs => hs.1), ?_, fun _ hs => hs.2⟩
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨i, hi⟩ := hs.2
    exact mem_iUnion.mpr ⟨i, hi hxs⟩
  · intro hx
    have hxR : x ∈ R.space := by
      rw [hRK.space_eq]
      exact interior_subset (hUK hx)
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    have hHi : ∀ A ∈ H i, R.RespectsAffineHyperplane A := fun A hA =>
      hRH A (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hA⟩)
    have hxiH : ∀ A ∈ H i, A x ≤ 0 := by rwa [hH i] at hxi
    obtain ⟨s, hs, hxs, hverts⟩ := R.exists_face_in_halfspaces (H i) hHi hxR hxiH
    have hsT : (s : Set E) ⊆ convexHull ℝ (T i : Set E) := by
      intro v hv
      rw [hH i]
      exact hverts v hv
    exact mem_space_iff.mpr ⟨s,
      ⟨hs, i, convexHull_min hsT (convex_convexHull ℝ _)⟩, hxs⟩




theorem exists_finite_triangulation_iUnion {ι : Type*} [Finite ι]
    (K : ι → SimplicialComplex ℝ E) (hK : ∀ i, (K i).faces.Finite) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = ⋃ i, (K i).space ∧
      ∀ s ∈ L.faces, ∃ i, ∃ t ∈ (K i).faces,
        convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  classical
  let : ∀ i, Finite (K i).faces := fun i => (hK i).to_subtype
  let T : (Σ i, (K i).faces) → Finset E := fun p => p.2.val
  obtain ⟨L, hL, hspace, hfaces⟩ := exists_finite_triangulation_iUnion_convexHull T
    (fun p => (K p.1).indep p.2.property)
  refine ⟨L, hL, hspace.trans ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨p.1, (K p.1).convexHull_subset_space p.2.property hp⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hi
      exact mem_iUnion.mpr ⟨⟨i, s, hs⟩, hxs⟩
  · intro s hs
    obtain ⟨p, hp⟩ := hfaces s hs
    exact ⟨p.1, p.2.val, p.2.property, hp⟩




theorem exists_finite_triangulation_union (K J : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hJ : J.faces.Finite) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∪ J.space := by
  let C : Bool → SimplicialComplex ℝ E := fun b => if b then K else J
  have hC (b : Bool) : (C b).faces.Finite := by cases b <;> assumption
  obtain ⟨L, hL, hspace, _⟩ := exists_finite_triangulation_iUnion C hC
  refine ⟨L, hL, hspace.trans ?_⟩
  ext x
  simp only [mem_iUnion, Bool.exists_bool, C, Bool.false_eq_true, if_false, if_true,
    mem_union]
  exact or_comm

end Geometry.SimplicialComplex
