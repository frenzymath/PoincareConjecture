import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Ambient
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

private theorem finite_bounded_side_subset_ball
    {S A B : Set (EuclideanSpace ℝ (Fin 3))} {r : ℝ} (hr : 0 < r)
    (hSr : S ⊆ ball 0 r) (hA : IsOpen A) (hB : IsOpen B)
    (hdis : Disjoint A B) (hcover : A ∪ B = Sᶜ) (hbounded : Bornology.IsBounded A) :
    A ⊆ ball 0 r := by
  have hout : {x : EuclideanSpace ℝ (Fin 3) | r ≤ ‖x‖} ⊆ A ∪ B := by
    intro x hx
    rw [hcover]
    intro hxS
    have h := hSr hxS
    simp only [mem_ball, dist_zero_right] at h
    exact (not_le_of_gt h) hx
  have hpre := Poincare.Topology.isPreconnected_norm_ge
    (E := EuclideanSpace ℝ (Fin 3)) (by rw [← Module.finrank_eq_rank]; simp) hr
  rcases hpre.subset_or_subset hA hB hdis hout with hleft | hright
  · have hwhole : (univ : Set (EuclideanSpace ℝ (Fin 3))) ⊆ ball 0 r ∪ A := by
      intro x _
      by_cases hx : ‖x‖ < r
      · exact Or.inl (by simpa only [mem_ball, dist_zero_right] using hx)
      · exact Or.inr (hleft (le_of_not_gt hx))
    exact False.elim (NormedSpace.unbounded_univ ℝ (EuclideanSpace ℝ (Fin 3))
      ((isBounded_ball.union hbounded).subset hwhole))
  · intro x hx
    simp only [mem_ball, dist_zero_right]
    by_contra h
    exact Set.disjoint_left.mp hdis hx (hright (le_of_not_gt h))

private theorem finite_inverse_frontier
    {M : Type u} [TopologicalSpace M] [T2Space M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    {B : Set (EuclideanSpace ℝ (Fin 3))} (hcompact : IsCompact (closure B))
    (htarget : closure B ⊆ c.target) :
    IsCompact (closure (c.symm '' B)) ∧
      frontier (c.symm '' B) = c.symm '' frontier B := by
  have himage : c.symm.IsImage B (c.symm '' B) := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (c.symm.injOn (htarget (subset_closure hy)) hx hxy) ▸ hy
    · exact mem_image_of_mem c.symm
  have hclosure : closure (c.symm '' B) = c.symm '' closure B :=
    (image_closure_of_isCompact hcompact (c.symm.continuousOn.mono htarget)).symm
  have hsource : closure (c.symm '' B) ⊆ c.source := by
    rw [hclosure]
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_target (htarget hx)
  refine ⟨?_, ?_⟩
  · rw [hclosure]
    exact hcompact.image_of_continuousOn (c.symm.continuousOn.mono htarget)
  · symm
    simpa only [OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.symm_target,
      inter_eq_right.mpr (frontier_subset_closure.trans htarget),
      inter_eq_right.mpr (frontier_subset_closure.trans hsource)] using
      himage.frontier.image_eq

theorem limitFinite_neck_local_bounded_side
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcapture : N.carrier ⊆ c.source) {r : ℝ} (hr : 0 < r)
    (htarget : closedBall (0 : EuclideanSpace ℝ (Fin 3)) r ⊆ c.target)
    (hsphere : c '' N.central_sphere ⊆ ball 0 r) :
    ∃ A : Set M, IsOpen A ∧ IsCompact (closure A) ∧
      A ⊆ c.symm '' ball 0 r ∧ frontier A = N.central_sphere ∧
      (N.region (-N.epsilon⁻¹) 0 ⊆ A ∨ N.region 0 N.epsilon⁻¹ ⊆ A) := by
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let e : NeckDomain N.epsilon ≃ₜ (c '' N.carrier) :=
    N.coordinate.trans (c.homeomorphOfImageSubsetSource hcapture rfl)
  have hcenter : range (fun y : UnitTwoSphere =>
      (e (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
        inv_pos.mpr N.epsilon_pos⟩) : EuclideanSpace ℝ (Fin 3))) =
      c '' N.central_sphere := by
    change range (fun y : UnitTwoSphere => c (N.coordinate
      (y, ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos),
        inv_pos.mpr N.epsilon_pos⟩) : M)) = _
    rw [Set.range_comp', N.coordinate_central_range]
  have hnegative : (fun z : NeckDomain N.epsilon =>
      (e z : EuclideanSpace ℝ (Fin 3))) '' {z | (z.2 : ℝ) < 0} =
      c '' N.region (-N.epsilon⁻¹) 0 := by
    change (fun z : NeckDomain N.epsilon => c (N.coordinate z : M)) '' _ = _
    rw [← image_image, N.coordinate_negative_image]
  have hpositive : (fun z : NeckDomain N.epsilon =>
      (e z : EuclideanSpace ℝ (Fin 3))) '' {z | 0 < (z.2 : ℝ)} =
      c '' N.region 0 N.epsilon⁻¹ := by
    change (fun z : NeckDomain N.epsilon => c (N.coordinate z : M)) '' _ = _
    rw [← image_image, N.coordinate_positive_image]
  have hsep := Poincare.Topology.exists_collar_complementary_regions
    (inv_pos.mpr N.epsilon_pos)
    (c.isOpen_image_of_subset_source N.carrier_open hcapture) e
  dsimp only at hsep
  rw [hcenter, hnegative, hpositive] at hsep
  obtain ⟨A, B, hA, hB, _, _, hdis, hcover, hfA, hfB, hneg, hpos⟩ := hsep
  have hcompact : IsCompact (c '' N.central_sphere) :=
    N.isCompact_central_sphere.image_of_continuousOn
      (c.continuousOn.mono (N.central_sphere_subset.trans hcapture))
  have hchoice : ∃ V : Set (EuclideanSpace ℝ (Fin 3)),
      IsOpen V ∧ Bornology.IsBounded V ∧ V ⊆ ball 0 r ∧
      frontier V = c '' N.central_sphere ∧
      (c '' N.region (-N.epsilon⁻¹) 0 ⊆ V ∨ c '' N.region 0 N.epsilon⁻¹ ⊆ V) := by
    rcases Poincare.Topology.bounded_side_of_compact_complement_partition_euclidean_three
      hcompact hA hB hdis hcover with ⟨hbound, _⟩ | ⟨hbound, _⟩
    · exact ⟨A, hA, hbound, finite_bounded_side_subset_ball hr hsphere hA hB hdis
        hcover hbound, hfA, Or.inl hneg⟩
    · exact ⟨B, hB, hbound, finite_bounded_side_subset_ball hr hsphere hB hA hdis.symm
        ((union_comm B A).trans hcover) hbound, hfB, Or.inr hpos⟩
  obtain ⟨V, hV, hVbounded, hVball, hVfront, hVhalf⟩ := hchoice
  have hVtarget : closure V ⊆ c.target :=
    ((closure_mono hVball).trans closure_ball_subset_closedBall).trans htarget
  obtain ⟨hcompactInverse, hfrontInverse⟩ :=
    finite_inverse_frontier c hVbounded.isCompact_closure hVtarget
  have hroundtrip : c.symm '' (c '' N.central_sphere) = N.central_sphere := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa only [c.left_inv (hcapture (N.central_sphere_subset hy))] using hy
    · intro hx
      exact ⟨c x, mem_image_of_mem c hx,
        c.left_inv (hcapture (N.central_sphere_subset hx))⟩
  refine ⟨c.symm '' V,
    c.isOpen_image_symm_of_subset_target hV (subset_closure.trans hVtarget),
    hcompactInverse, image_mono hVball,
    hfrontInverse.trans (by rw [hVfront, hroundtrip]), ?_⟩
  rcases hVhalf with hnegV | hposV
  · left
    intro x hx
    exact ⟨c x, hnegV (mem_image_of_mem c hx), c.left_inv (hcapture hx.1)⟩
  · right
    intro x hx
    exact ⟨c x, hposV (mem_image_of_mem c hx), c.left_inv (hcapture hx.1)⟩

end PoincareConjecture.M47
