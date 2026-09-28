import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarCarrierNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIntrinsicDensity

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem face_mem_subcomplex_of_intrinsicInterior (R Q : SimplicialComplex ℝ E)
    (hQR : Q ≤ R) {s : Finset E} (hs : s ∈ R.faces) {x : E}
    (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxQ : x ∈ Q.space) : s ∈ Q.faces := by
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxQ
  exact Q.down_closed ht (R.subset_of_mem_intrinsicInterior_face hs (hQR ht) hxs hxt)
    (R.nonempty_of_mem_faces hs)

variable [FiniteDimensional ℝ E]

theorem le_of_common_subcomplex_space_subset (R B Q : SimplicialComplex ℝ E)
    (hBR : B ≤ R) (hQR : Q ≤ R) (hspace : B.space ⊆ Q.space) : B ≤ Q := by
  intro s hs
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
    (Finset.coe_nonempty.mpr (B.nonempty_of_mem_faces hs)).convexHull
  exact R.face_mem_subcomplex_of_intrinsicInterior Q hQR (hBR hs) hx
    (hspace (convexHull_subset_space hs (intrinsicInterior_subset hx)))

variable [DecidableEq E]

theorem face_mem_retained_edge_of_incident (J R B Q : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hdim : ∀ t ∈ J.faces, t.card ≤ 2)
    (hBR : B ≤ R) (hQR : Q ≤ R) (hB : B.space ⊆ J.space)
    {e : Finset E} (he : e ∈ J.faces) (hecard : e.card = 2)
    (hQ : Q.space = convexHull ℝ (e : Set E))
    {q : E} (hq : q ∈ intrinsicInterior ℝ (convexHull ℝ (e : Set E)))
    {s : Finset E} (hs : s ∈ B.faces) (hqs : q ∈ s) : s ∈ Q.faces := by
  classical
  let T := hJ.toFinset.filter (fun t => ¬ e ⊆ t)
  let D := ⋃ t ∈ T, convexHull ℝ (t : Set E)
  have hD : IsClosed D :=
    (T.finite_toSet.isCompact_biUnion (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed
  have hqD : q ∉ D := by
    intro h
    obtain ⟨t, ht, hqt⟩ := mem_iUnion₂.mp h
    obtain ⟨htJ, hnot⟩ := Finset.mem_filter.mp ht
    exact hnot (J.subset_of_mem_intrinsicInterior_face he (hJ.mem_toFinset.mp htJ) hq hqt)
  obtain ⟨x, hxs, hxD⟩ :=
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior_inter_open_nonempty
      hD.isOpen_compl ⟨q, subset_convexHull ℝ (s : Set E) hqs, hqD⟩
  have hxJ := hB (convexHull_subset_space hs (intrinsicInterior_subset hxs))
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxJ
  have het : e ⊆ t := by
    by_contra h
    exact hxD (mem_iUnion₂.mpr ⟨t,
      Finset.mem_filter.mpr ⟨hJ.mem_toFinset.mpr ht, h⟩, hxt⟩)
  have het' : e = t := Finset.eq_of_subset_of_card_le het (by rw [hecard]; exact hdim t ht)
  apply R.face_mem_subcomplex_of_intrinsicInterior Q hQR (hBR hs) hxs
  rw [hQ, het']
  exact hxt

theorem retained_edge_star_eq (J R B Q : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hdim : ∀ t ∈ J.faces, t.card ≤ 2)
    (hBR : B ≤ R) (hQR : Q ≤ R) (hB : B.space = J.space)
    {e : Finset E} (he : e ∈ J.faces) (hecard : e.card = 2)
    (hQ : Q.space = convexHull ℝ (e : Set E))
    {q : E} (hq : q ∈ intrinsicInterior ℝ (convexHull ℝ (e : Set E))) :
    {s : Finset E | s ∈ B.faces ∧ q ∈ s} =
      {s : Finset E | s ∈ Q.faces ∧ q ∈ s} := by
  have hQB : Q ≤ B := R.le_of_common_subcomplex_space_subset Q B hQR hBR (by
    rw [hQ, hB]
    exact convexHull_subset_space he)
  ext s
  exact ⟨fun hs => ⟨J.face_mem_retained_edge_of_incident R B Q hJ hdim hBR hQR
    hB.subset he hecard hQ hq hs.1 hs.2, hs.2⟩,
    fun hs => ⟨hQB hs.1, hs.2⟩⟩

theorem retained_edge_edgeStar_eq (J R B Q : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hdim : ∀ t ∈ J.faces, t.card ≤ 2)
    (hBR : B ≤ R) (hQR : Q ≤ R) (hB : B.space = J.space)
    {e : Finset E} (he : e ∈ J.faces) (hecard : e.card = 2)
    (hQ : Q.space = convexHull ℝ (e : Set E))
    {q : E} (hq : q ∈ intrinsicInterior ℝ (convexHull ℝ (e : Set E))) :
    {s : Finset E | s ∈ B.faces ∧ s.card = 2 ∧ q ∈ s} =
      {s : Finset E | s ∈ Q.faces ∧ s.card = 2 ∧ q ∈ s} := by
  have hstar := J.retained_edge_star_eq R B Q hJ hdim hBR hQR hB he hecard hQ hq
  ext s
  have hs := Set.ext_iff.mp hstar s
  change (s ∈ B.faces ∧ q ∈ s) ↔ (s ∈ Q.faces ∧ q ∈ s) at hs
  exact ⟨fun h => ⟨(hs.mp ⟨h.1, h.2.2⟩).1, h.2⟩,
    fun h => ⟨(hs.mpr ⟨h.1, h.2.2⟩).1, h.2⟩⟩

end Geometry.SimplicialComplex
