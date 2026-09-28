import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SmoothDisjointUnionData

variable {n m : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
  {sides : Fin m → GeneralizedSliceCarrier.{u}} {A : GeneralizedSliceCarrier.{u}}
  (D : SmoothDisjointUnionData pieces A)

theorem existsUnique_region_of_isConnected {K : Set A.carrier}
    (hK : IsConnected K) : ∃! i : Fin n, K ⊆ D.region i := by
  obtain ⟨x, hx⟩ := hK.nonempty
  have hxcover : x ∈ ⋃ i, D.region i := D.cover.symm ▸ mem_univ x
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxcover
  have hsub : K ⊆ D.region i := hK.isPreconnected.subset_isClopen
    ⟨D.region_closed i, D.region_open i⟩ ⟨x, hx, hi⟩
  refine ⟨i, hsub, ?_⟩
  intro j hj
  by_contra hji
  exact Set.disjoint_left.mp (D.pairwise_disjoint j i hji) (hj hx) hi

theorem region_isPreconnected (i : Fin n)
    (hi : IsPreconnected (univ : Set (pieces i).carrier)) :
    IsPreconnected (D.region i) := by
  rw [← (D.identify i).map_image]
  exact hi.image _ (D.identify i).map_smooth.continuousOn

theorem existsUnique_region_for_surgeryBall
    (E : SmoothDisjointUnionData sides A) (j : Fin m)
    (B : SurgeryBallEmbedding (sides j)) :
    ∃! i : Fin n,
      (E.identify j).map '' (B.map '' ball (0 : StandardCapSpace) 2) ⊆ D.region i := by
  apply D.existsUnique_region_of_isConnected
  have hball : IsConnected (ball (0 : StandardCapSpace) 2) :=
    (convex_ball (0 : StandardCapSpace) 2).isConnected
      (nonempty_ball.mpr (by norm_num))
  exact (hball.image B.map B.map_smooth.continuousOn).image _
    ((E.identify j).map_smooth.continuousOn.mono (subset_univ _))

theorem region_subset_region_of_map_mem
    (E : SmoothDisjointUnionData sides A) {i : Fin n} {j : Fin m}
    (hi : IsPreconnected (univ : Set (pieces i).carrier))
    (x : (sides j).carrier) (hx : (E.identify j).map x ∈ D.region i) :
    D.region i ⊆ E.region j := by
  apply (D.region_isPreconnected i hi).subset_isClopen
    ⟨E.region_closed j, E.region_open j⟩
  refine ⟨(E.identify j).map x, hx, ?_⟩
  exact (E.identify j).map_image.subset (mem_image_of_mem _ (mem_univ x))

theorem surgeryBall_closedBall_subset_region
    (E : SmoothDisjointUnionData sides A) {i : Fin n} {j : Fin m}
    (B : SurgeryBallEmbedding (sides j))
    (hi : (E.identify j).map '' (B.map '' ball (0 : StandardCapSpace) 2) ⊆ D.region i) :
    (E.identify j).map '' B.closedBall ⊆ D.region i := by
  apply Subset.trans (image_mono (image_mono ?_)) hi
  exact closedBall_subset_ball (by norm_num : (1 : ℝ) < 2)

theorem exists_region_for_surgeryBall
    (E : SmoothDisjointUnionData sides A)
    (hpieces : ∀ i, IsPreconnected (univ : Set (pieces i).carrier))
    (j : Fin m) (B : SurgeryBallEmbedding (sides j)) :
    ∃ i : Fin n,
      (E.identify j).map '' (B.map '' ball (0 : StandardCapSpace) 2) ⊆ D.region i ∧
      (E.identify j).map '' B.closedBall ⊆ D.region i ∧
      D.region i ⊆ E.region j := by
  obtain ⟨i, hi, _⟩ := D.existsUnique_region_for_surgeryBall E j B
  refine ⟨i, hi, D.surgeryBall_closedBall_subset_region E B hi, ?_⟩
  apply D.region_subset_region_of_map_mem E (hpieces i) (B.map 0)
  apply hi
  exact mem_image_of_mem _ (mem_image_of_mem _ (by simp))

theorem surgeryBall_region_ne
    (E : SmoothDisjointUnionData sides A)
    (hpieces : ∀ i, IsPreconnected (univ : Set (pieces i).carrier))
    {a b : Fin m} (hab : a ≠ b)
    (Ba : SurgeryBallEmbedding (sides a)) (Bb : SurgeryBallEmbedding (sides b))
    {i k : Fin n}
    (hi : (E.identify a).map '' (Ba.map '' ball (0 : StandardCapSpace) 2) ⊆ D.region i)
    (hk : (E.identify b).map '' (Bb.map '' ball (0 : StandardCapSpace) 2) ⊆ D.region k) :
    i ≠ k := by
  intro hik
  subst k
  have hside : D.region i ⊆ E.region a :=
    D.region_subset_region_of_map_mem E (hpieces i) (Ba.map 0)
      (hi (mem_image_of_mem _ (mem_image_of_mem _ (by simp))))
  have hfirst : (E.identify b).map (Bb.map 0) ∈ E.region a :=
    hside (hk (mem_image_of_mem _ (mem_image_of_mem _ (by simp))))
  have hsecond : (E.identify b).map (Bb.map 0) ∈ E.region b :=
    (E.identify b).map_image.subset (mem_image_of_mem _ (mem_univ _))
  exact Set.disjoint_left.mp (E.pairwise_disjoint a b hab) hfirst hsecond

end PoincareConjecture.SmoothDisjointUnionData
