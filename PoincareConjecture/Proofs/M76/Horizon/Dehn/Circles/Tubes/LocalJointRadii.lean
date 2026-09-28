import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BarycentricEdgeLabels
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualBlocks
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIntervals
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc

set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex



theorem dual_interval_eq_centroid_segments
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (hI : IsFinitePLBallPair ℝ (K.barycentricDualBlock s).space
      {t.centroid ℝ id, u.centroid ℝ id})
    (hm : s.centroid ℝ id ∈ (K.barycentricDualBlock s).space \
      {t.centroid ℝ id, u.centroid ℝ id}) :
    (K.barycentricDualBlock s).space =
      segment ℝ (s.centroid ℝ id) (t.centroid ℝ id) ∪
        segment ℝ (s.centroid ℝ id) (u.centroid ℝ id) ∧
    segment ℝ (s.centroid ℝ id) (t.centroid ℝ id) ∩
        segment ℝ (s.centroid ℝ id) (u.centroid ℝ id) = {s.centroid ℝ id} := by
  classical
  let m := s.centroid ℝ id
  let a := t.centroid ℝ id
  let b := u.centroid ℝ id
  have hma : m ≠ a := fun h => hm.2 (Or.inl h)
  have hmb : m ≠ b := fun h => hm.2 (Or.inr h)
  have hab : a ≠ b := by
    intro h
    exact htu (congrArg Subtype.val (K.faceCentroid_injective
      (a₁ := ⟨t, ht⟩) (a₂ := ⟨u, hu⟩) h))
  have hedge (v : Finset E) (hv : v ∈ K.faces) (hsv : s ⊆ v) :
      ({m, v.centroid ℝ id} : Finset E) ∈ (K.barycentricDualBlock s).faces := by
    refine ⟨(K.barycentric_centroid_pair_face_iff ⟨s, hs⟩ ⟨v, hv⟩).mpr (Or.inl hsv), ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · exact ⟨s, hs, Subset.rfl, hz.symm⟩
    · exact ⟨v, hv, hsv, (Finset.mem_singleton.mp hz).symm⟩
  have hsub (v : Finset E) (hv : v ∈ K.faces) (hsv : s ⊆ v) :
      segment ℝ m (v.centroid ℝ id) ⊆ (K.barycentricDualBlock s).space := by
    simpa only [Finset.coe_pair, convexHull_pair] using
      (K.barycentricDualBlock s).convexHull_subset_space (hedge v hv hsv)
  have hinter : segment ℝ m a ∩ segment ℝ m b = {m} := by
    apply Subset.antisymm
    · intro z hz
      have h := K.barycentricSubdivision.inter_subset_convexHull (hedge t ht hst).1
        (hedge u hu hsu).1
        ⟨by simpa only [Finset.coe_pair, convexHull_pair] using hz.1,
          by simpa only [Finset.coe_pair, convexHull_pair] using hz.2⟩
      have hpair : ({m, a} : Set E) ∩ {m, b} = {m} := by
        ext w
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        aesop
      simp only [Finset.coe_pair] at h
      change z ∈ convexHull ℝ (({m, a} : Set E) ∩ {m, b}) at h
      simpa only [hpair, convexHull_singleton] using h
    · rintro z rfl
      exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  have hsegments := isFinitePLBallPair_two_segments hma.symm hmb (by
    simpa only [segment_symm (𝕜 := ℝ) a m] using hinter)
  have hsegments' : IsFinitePLBallPair ℝ (segment ℝ m a ∪ segment ℝ m b) {a, b} := by
    simpa only [segment_symm (𝕜 := ℝ) a m] using hsegments
  exact ⟨(hsegments'.eq_of_subset_with_same_endpoints hI
    (union_subset (hsub t ht hst) (hsub u hu hsu)) hab).symm, hinter⟩

end Geometry.SimplicialComplex
