import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexFacets










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [DecidableEq E] in




theorem full_coface_eq_of_paired_facet
    (K : SimplicialComplex ℝ E) {s t u w : Finset E}
    (hscard : s.card = Module.finrank ℝ E)
    (ht : t ∈ K.faces) (hu : u ∈ K.faces) (hw : w ∈ K.faces)
    (htcard : t.card = Module.finrank ℝ E + 1)
    (hucard : u.card = Module.finrank ℝ E + 1)
    (hwcard : w.card = Module.finrank ℝ E + 1)
    (hst : s ⊆ t) (hsu : s ⊆ u) (hsw : s ⊆ w) (htu : t ≠ u)
    {x : E} (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E))) :
    w = t ∨ w = u := by
  have hxint := K.mem_interior_union_of_paired_facet
    hscard ht hu htcard hucard hst hsu htu hxs
  obtain ⟨y, hyw, hyint⟩ :=
    (convex_convexHull ℝ (w : Set E)).intrinsicInterior_inter_open_nonempty
      isOpen_interior ⟨x, convexHull_mono hsw (intrinsicInterior_subset hxs), hxint⟩
  rcases interior_subset hyint with hyt | hyu
  · exact Or.inl (Finset.eq_of_subset_of_card_le
      (K.subset_of_mem_intrinsicInterior_face hw ht hyw hyt) (by omega))
  · exact Or.inr (Finset.eq_of_subset_of_card_le
      (K.subset_of_mem_intrinsicInterior_face hw hu hyw hyu) (by omega))





theorem faceLink_ncard_eq_two_of_hull_meets_interior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = Module.finrank ℝ E)
    (hmeet : (convexHull ℝ (s : Set E) ∩ interior K.space).Nonempty) :
    (K.faceLink s).vertices.ncard = 2 := by
  classical
  obtain ⟨x, hxs, hxint⟩ :=
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior_inter_open_nonempty
      isOpen_interior hmeet
  obtain ⟨t, ht, u, hu, hst, hsu, htcard, hucard, htu⟩ :=
    K.hasTwoFullCofaces_of_mem_interior hK hs hscard hxs hxint
  obtain ⟨p, hps, hpt⟩ := Finset.exists_eq_insert_iff.mpr
    (And.intro hst (show s.card + 1 = t.card by omega))
  obtain ⟨q, hqs, hqu⟩ := Finset.exists_eq_insert_iff.mpr
    (And.intro hsu (show s.card + 1 = u.card by omega))
  have hpq : p ≠ q := by
    intro he
    apply htu
    rw [← hpt, ← hqu, he]
  have hpoint {v : E} (hvs : v ∉ s) (hface : insert v s ∈ K.faces) :
      v ∈ (K.faceLink s).vertices := by
    refine ⟨K.down_closed hface (Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_self v s)) (Finset.singleton_nonempty v), ?_, ?_⟩
    · simpa using hvs
    · simpa only [Finset.union_singleton] using hface
  have hp : p ∈ (K.faceLink s).vertices := hpoint hps (hpt.symm ▸ ht)
  have hq : q ∈ (K.faceLink s).vertices := hpoint hqs (hqu.symm ▸ hu)
  have hset : (K.faceLink s).vertices = {p, q} := by
    ext v
    constructor
    · intro hv
      have hvs : v ∉ s := (K.faceLink_vertices_subset s hv).2
      have hw : insert v s ∈ K.faces := by
        simpa only [Finset.union_singleton] using hv.2.2
      have hwcard : (insert v s).card = Module.finrank ℝ E + 1 := by
        rw [Finset.card_insert_of_notMem hvs, hscard]
      rcases K.full_coface_eq_of_paired_facet hscard ht hu hw htcard hucard hwcard
        hst hsu (Finset.subset_insert v s) htu hxs with he | he
      · have hvp : v ∈ insert p s := (he.trans hpt.symm) ▸ Finset.mem_insert_self v s
        exact Or.inl ((Finset.mem_insert.mp hvp).resolve_right hvs)
      · have hvq : v ∈ insert q s := (he.trans hqu.symm) ▸ Finset.mem_insert_self v s
        exact Or.inr ((Finset.mem_insert.mp hvq).resolve_right hvs)
    · rintro (rfl | rfl)
      · exact hp
      · exact hq
  exact ncard_eq_two.mpr ⟨p, q, hpq, hset⟩

end Geometry.SimplicialComplex
