import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem mem_vertices_of_finite_subcomplex_intersection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K A B : SimplicialComplex ℝ E} (hAK : A ≤ K) (hBK : B ≤ K)
    (hfinite : (A.space ∩ B.space).Finite) {x : E}
    (hxA : x ∈ A.space) (hxB : x ∈ B.space) :
    x ∈ A.vertices ∧ x ∈ B.vertices := by
  classical
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxA
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxB
  have hxu : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    simpa only [Finset.coe_inter] using
      K.inter_subset_convexHull (hAK hs) (hBK ht) ⟨hxs, hxt⟩
  have hne : (s ∩ t).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxu⟩)
  have huA : s ∩ t ∈ A.faces := A.down_closed hs Finset.inter_subset_left hne
  have huB : s ∩ t ∈ B.faces := B.down_closed ht Finset.inter_subset_right hne
  have hsmall : MapsTo id (convexHull ℝ ((s ∩ t : Finset E) : Set E))
      (A.space ∩ B.space) :=
    fun _ hy => ⟨A.convexHull_subset_space huA hy, B.convexHull_subset_space huB hy⟩
  have heq : s ∩ t = {x} := by
    apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    refine ⟨hne, ?_⟩
    intro y hy
    exact (convex_convexHull ℝ ((s ∩ t : Finset E) : Set E)).isPreconnected.constant_of_mapsTo
      hfinite.isDiscrete continuousOn_id hsmall (subset_convexHull ℝ _ hy) hxu
  constructor
  · change {x} ∈ A.faces
    rwa [heq] at huA
  · change {x} ∈ B.faces
    rwa [heq] at huB

end Geometry.SimplicialComplex
