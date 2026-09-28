import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem existsUnique_edge_intrinsicInterior_of_not_vertex
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hdim : ∀ s ∈ J.faces, s.card ≤ 2) {q : E}
    (hq : q ∈ J.space) (hqv : q ∉ J.vertices) :
    ∃! s : Finset E, s ∈ J.faces ∧ s.card = 2 ∧
      q ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨s, hs, hqs⟩ := J.exists_face_intrinsicInterior_of_finite hJ hq
  have hcpos := Finset.card_pos.mpr (J.nonempty_of_mem_faces hs)
  have hcle := hdim s hs
  have hcne : s.card ≠ 1 := by
    intro h
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h
    have hqv' : q = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        (intrinsicInterior_subset hqs)
    exact hqv (hqv'.symm ▸ hs)
  have hcard : s.card = 2 := by omega
  refine ⟨s, ⟨hs, hcard, hqs⟩, ?_⟩
  rintro t ⟨ht, htc, hqt⟩
  exact Finset.eq_of_subset_of_card_le
    (J.subset_of_mem_intrinsicInterior_face ht hs hqt (intrinsicInterior_subset hqs)) (by omega)

variable [FiniteDimensional ℝ E] [DecidableEq E]



theorem refined_boundary_edge_has_unmarked_vertex
    (J R B : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hdim : ∀ s ∈ J.faces, s.card ≤ 2) (hBR : B ≤ R) (hB : B.space = J.space)
    (Q : {s : J.faces // s.val.card = 2} → SimplicialComplex ℝ E)
    (hQR : ∀ s, Q s ≤ R)
    (hQ : ∀ s, (Q s).space = convexHull ℝ (s.val.val : Set E))
    (Z : Set E) (hvertices : Disjoint J.vertices Z)
    (hmarks : ∀ s ∈ J.faces, s.card = 2 →
      ∀ x ∈ convexHull ℝ (s : Set E), x ∈ Z →
      ∀ y ∈ convexHull ℝ (s : Set E), y ∈ Z → x = y) :
    ∀ s ∈ B.faces, s.card = 2 → ∃ q ∈ s, q ∉ Z := by
  intro s hs hcard
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
  by_cases hu : u ∉ Z
  · exact ⟨u, by simp, hu⟩
  by_cases hv : v ∉ Z
  · exact ⟨v, by simp, hv⟩
  have huZ : u ∈ Z := not_not.mp hu
  have hvZ : v ∈ Z := not_not.mp hv
  have huJ : u ∈ J.space := hB.subset
    (B.convexHull_subset_space hs (subset_convexHull ℝ _ (by simp)))
  have hunot : u ∉ J.vertices := fun h => disjoint_left.mp hvertices h huZ
  obtain ⟨e, ⟨he, hecard, hue⟩, _⟩ :=
    J.existsUnique_edge_intrinsicInterior_of_not_vertex hJ hdim huJ hunot
  let i : {s : J.faces // s.val.card = 2} := ⟨⟨e, he⟩, hecard⟩
  have hsQ := J.face_mem_retained_edge_of_incident R B (Q i) hJ hdim hBR
    (hQR i) hB.subset he hecard (hQ i) hue hs (by simp)
  have huQ : u ∈ convexHull ℝ (e : Set E) := (hQ i).subset
    ((Q i).convexHull_subset_space hsQ (subset_convexHull ℝ _ (by simp)))
  have hvQ : v ∈ convexHull ℝ (e : Set E) := (hQ i).subset
    ((Q i).convexHull_subset_space hsQ (subset_convexHull ℝ _ (by simp)))
  exact (huv (hmarks e he hecard u huQ huZ v hvQ hvZ)).elim

end Geometry.SimplicialComplex
