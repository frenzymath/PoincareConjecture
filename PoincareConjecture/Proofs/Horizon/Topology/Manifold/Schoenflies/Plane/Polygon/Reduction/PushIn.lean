import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.CornerPush
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.VertexReplacement

set_option autoImplicit false

open Set
open scoped ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}

noncomputable def polygonPushVertex (p : Polygon E n) (k : Fin n) (t : ℝ) : Polygon E n :=
  polygonReplaceVertex p k (cornerPushPoint (p k) (p ((finRotate n).symm k))
    (p (finRotate n k)) t)

theorem polygonPushVertex_zero (p : Polygon E n) (k : Fin n) :
    polygonPushVertex p k 0 = p := by
  rw [polygonPushVertex, cornerPushPoint_zero, polygonReplaceVertex_self]

theorem polygonPushVertex_one_vertex (p : Polygon E n) (k : Fin n) :
    polygonPushVertex p k 1 k = midpoint ℝ (p ((finRotate n).symm k)) (p (finRotate n k)) := by
  rw [polygonPushVertex, polygonReplaceVertex_apply_same, cornerPushPoint_one]

theorem polygonPushVertex_boundary_sdiff_triangle (p : Polygon E n) (k : Fin n)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    (polygonPushVertex p k t).boundary ℝ \ polygonVertexTriangle p k =
      p.boundary ℝ \ polygonVertexTriangle p k := by
  let T := polygonVertexTriangle p k
  let v := cornerPushPoint (p k) (p ((finRotate n).symm k)) (p (finRotate n k)) t
  let q := polygonReplaceVertex p k v
  have hconv : Convex ℝ T := convex_convexHull ℝ _
  have hk : p k ∈ T := subset_convexHull ℝ _ (by simp)
  have hp : p ((finRotate n).symm k) ∈ T := subset_convexHull ℝ _ (by simp)
  have hs : p (finRotate n k) ∈ T := subset_convexHull ℝ _ (by simp)
  have hv : v ∈ T := cornerPushPoint_mem_triangle _ _ _ ht
  have hqother (j : Fin n) (hj : j ≠ k) : q j = p j :=
    polygonReplaceVertex_apply_of_ne p k v hj
  have hqmem (j : Fin n) (hj : p j ∈ T) : q j ∈ T := by
    by_cases hjk : j = k
    · subst j
      rw [show q k = v from polygonReplaceVertex_apply_same p k v]
      exact hv
    · rw [hqother j hjk]
      exact hj
  have hends (i : Fin n) (hi : i = k ∨ finRotate n i = k) :
      p i ∈ T ∧ p (finRotate n i) ∈ T := by
    rcases hi with hi | hi
    · subst i
      exact ⟨hk, hs⟩
    · have hip : i = (finRotate n).symm k := by
        simpa only [Equiv.symm_apply_apply] using congrArg (finRotate n).symm hi
      rw [hip, Equiv.apply_symm_apply]
      exact ⟨hp, hk⟩
  have hpedge (i : Fin n) (hi : i = k ∨ finRotate n i = k) : p.edgeSet ℝ i ⊆ T := by
    change affineSegment ℝ (p i) (p (finRotate n i)) ⊆ T
    rw [affineSegment_eq_segment]
    exact hconv.segment_subset (hends i hi).1 (hends i hi).2
  have hqedge (i : Fin n) (hi : i = k ∨ finRotate n i = k) : q.edgeSet ℝ i ⊆ T := by
    change affineSegment ℝ (q i) (q (finRotate n i)) ⊆ T
    rw [affineSegment_eq_segment]
    exact hconv.segment_subset (hqmem i (hends i hi).1) (hqmem _ (hends i hi).2)
  have heq (i : Fin n) (hi : ¬ (i = k ∨ finRotate n i = k)) :
      q.edgeSet ℝ i = p.edgeSet ℝ i := by
    change affineSegment ℝ (q i) (q (finRotate n i)) = _
    rw [hqother i (not_or.mp hi).1, hqother _ (not_or.mp hi).2]
    rfl
  change q.boundary ℝ \ T = p.boundary ℝ \ T
  ext z
  constructor
  · rintro ⟨hz, hzT⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    by_cases hik : i = k ∨ finRotate n i = k
    · exact (hzT (hqedge i hik hi)).elim
    · rw [heq i hik] at hi
      exact ⟨mem_iUnion.mpr ⟨i, hi⟩, hzT⟩
  · rintro ⟨hz, hzT⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    by_cases hik : i = k ∨ finRotate n i = k
    · exact (hzT (hpedge i hik hi)).elim
    · rw [← heq i hik] at hi
      exact ⟨mem_iUnion.mpr ⟨i, hi⟩, hzT⟩

end Module

theorem IsSimplePolygon.isSimple_polygonPushVertex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {p : Polygon E n}
    (hp : IsSimplePolygon p) (k : Fin n) (had : IsAdmissibleVertex p k)
    {t : ℝ} (ht : t ∈ Icc 0 1) : IsSimplePolygon (polygonPushVertex p k t) := by
  have hpk : (finRotate n).symm k ≠ k := by
    intro h
    have hrot := congrArg (finRotate n) h
    rw [Equiv.apply_symm_apply] at hrot
    exact hp.hasNondegenerateEdges k (congrArg p hrot)
  have ha : p ((finRotate n).symm k) ≠ p k := fun h => hpk (hp.vertices_injective h)
  have hb : p (finRotate n k) ≠ p k := (hp.hasNondegenerateEdges k).symm
  have hneighbors := finRotate_symm_ne_apply_of_three_le hp.three_le k
  have hinter : segment ℝ (p k) (p ((finRotate n).symm k)) ∩
      segment ℝ (p k) (p (finRotate n k)) ⊆ {p k} := by
    rintro z ⟨hzp, hzs⟩
    have hzp' : z ∈ p.edgeSet ℝ ((finRotate n).symm k) := by
      rw [polygon_edgeSet_eq_segment, Equiv.apply_symm_apply, segment_symm]
      exact hzp
    have hends := hp.edges_inter _ k hpk
      ⟨hzp', (polygon_edgeSet_eq_segment p k).symm ▸ hzs⟩
    rw [Equiv.apply_symm_apply] at hends
    rcases hends.1 with hzp | hzk
    · rcases hends.2 with hzk | hzs
      · exact hzk
      · exact (hneighbors (hp.vertices_injective (hzp.symm.trans hzs))).elim
    · exact hzk
  have hcorner := cornerPushPoint_simple_corner ha hb hinter ht
  exact hp.isSimple_polygonReplaceVertex_of_admissible k had _
    (cornerPushPoint_mem_triangle _ _ _ ht) hcorner.1 hcorner.2.1 hcorner.2.2

theorem contDiff_polygonPushVertex_apply {W E : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {s : ℕ∞ω}
    {p : W → Polygon E n} {tau : W → ℝ} (k i : Fin n)
    (hp : ∀ j, ContDiff ℝ s (fun z => p z j)) (htau : ContDiff ℝ s tau) :
    ContDiff ℝ s (fun z => polygonPushVertex (p z) k (tau z) i) := by
  by_cases hik : i = k
  · subst i
    simpa only [polygonPushVertex, polygonReplaceVertex_apply_same] using
      contDiff_cornerPushPoint (hp k) (hp ((finRotate n).symm k)) (hp (finRotate n k)) htau
  · simpa only [polygonPushVertex, polygonReplaceVertex_apply_of_ne _ _ _ hik] using hp i

end Poincare.Manifold.Schoenflies.Plane
