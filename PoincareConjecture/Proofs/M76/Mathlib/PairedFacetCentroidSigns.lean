import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFacetInterior
import PoincareConjecture.Proofs.M76.Mathlib.AffineCentroidSign
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHalfspaceGeometry










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem paired_centroid_positive
    (K : SimplicialComplex ℝ E) {s t u : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hsc : s.card = Module.finrank ℝ E)
    (htc : t.card = Module.finrank ℝ E + 1)
    (huc : u.card = Module.finrank ℝ E + 1)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hzero : ∀ x ∈ s, A x = 0) :
    0 < A (t.centroid ℝ id) ∨ 0 < A (u.centroid ℝ id) := by
  classical
  have hside {v : Finset E} (hsv : s ⊆ v) (hvc : v.card = Module.finrank ℝ E + 1) :
      (∀ x ∈ v, A x ≤ 0) ∨ (∀ x ∈ v, 0 ≤ A x) := by
    obtain ⟨p, _, he⟩ := Finset.exists_eq_insert_iff.mpr
      ⟨hsv, by omega⟩
    by_cases hp : A p ≤ 0
    · left
      intro x hx
      rw [← he] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp
      · exact (hzero x hx).le
    · right
      intro x hx
      rw [← he] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (lt_of_not_ge hp).le
      · exact (hzero x hx).symm.le
  by_contra hnone
  have htzero : A (t.centroid ℝ id) ≤ 0 :=
    le_of_not_gt (fun h => hnone (Or.inl h))
  have huzero : A (u.centroid ℝ id) ≤ 0 :=
    le_of_not_gt (fun h => hnone (Or.inr h))
  have htneg := t.affine_nonpos_on_hull_of_centroid (K.nonempty_of_mem_faces ht)
    A (hside hst htc) htzero
  have huneg := u.affine_nonpos_on_hull_of_centroid (K.nonempty_of_mem_faces hu)
    A (hside hsu huc) huzero
  obtain ⟨x, hxs⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
    (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull
  have hxzero : A x = 0 := convexHull_min hzero
    ((convex_singleton (0 : ℝ)).affine_preimage A) (intrinsicInterior_subset hxs)
  have hxint := K.mem_interior_union_of_paired_facet hsc ht hu htc huc hst hsu htu hxs
  have hsub : convexHull ℝ (t : Set E) ∪ convexHull ℝ (u : Set E) ⊆ {y | A y ≤ 0} :=
    fun y hy => hy.elim (htneg y) (huneg y)
  have hlt := interior_mono hsub hxint
  rw [A.interior_nonpos hA] at hlt
  exact (ne_of_lt hlt) hxzero





theorem opposite_centroid_signs_of_paired_facet
    (K : SimplicialComplex ℝ E) {s t u : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hsc : s.card = Module.finrank ℝ E)
    (htc : t.card = Module.finrank ℝ E + 1)
    (huc : u.card = Module.finrank ℝ E + 1)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hzero : ∀ x ∈ s, A x = 0) :
    (A (t.centroid ℝ id) < 0 ∧ 0 < A (u.centroid ℝ id)) ∨
      (0 < A (t.centroid ℝ id) ∧ A (u.centroid ℝ id) < 0) := by
  have hpos := paired_centroid_positive K hs ht hu hsc htc huc hst hsu htu A hA hzero
  have hAneg : (-A).linear ≠ 0 := by simpa using hA
  have hneg := paired_centroid_positive K hs ht hu hsc htc huc hst hsu htu (-A)
    hAneg (by intro x hx; simp only [AffineMap.coe_neg, Pi.neg_apply, hzero x hx, neg_zero])
  simp only [AffineMap.coe_neg, Pi.neg_apply, neg_pos] at hneg
  rcases hpos with htpos | hupos <;> rcases hneg with htneg | huneg
  · exact (not_lt_of_ge htneg.le htpos).elim
  · exact Or.inr ⟨htpos, huneg⟩
  · exact Or.inl ⟨htneg, hupos⟩
  · exact (not_lt_of_ge huneg.le hupos).elim

end Geometry.SimplicialComplex
