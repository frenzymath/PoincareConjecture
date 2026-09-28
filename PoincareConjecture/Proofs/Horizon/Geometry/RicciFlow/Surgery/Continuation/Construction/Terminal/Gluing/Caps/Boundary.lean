import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Caps.Chart







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.MetricSurgeryResult

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

theorem interior_closed_cap :
    interior (closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))) =
      R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) := by
  have hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) =
      Metric.ball 0 R.capEuclideanRadius :=
    MetricSurgery.standard_ball_eq_euclidean g₀
      (by linarith [g₀.cylindrical_end.radius_pos])
  have hbig : IsOpen (g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) := by
    rw [MetricSurgery.standard_ball_eq_euclidean g₀
      (by linarith [g₀.cylindrical_end.radius_pos])]
    exact Metric.isOpen_ball
  have hopen : IsOpen (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) := by
    rw [hball]
    exact R.cap_image_isOpen Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans R.capEuclidean_closedBall_subset)
  refine Subset.antisymm ?_ (interior_maximal subset_closure hopen)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := R.capEuclidean_closedBall_image.superset (interior_subset hy)
  have hxc := (R.cap_map_smooth x (R.capEuclidean_closedBall_subset hx)).contMDiffAt
    (hbig.mem_nhds (R.capEuclidean_closedBall_subset hx))
  have hpre := hxc.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
  have hnhds : Metric.closedBall (0 : StandardCapSpace) R.capEuclideanRadius ∈ 𝓝 x := by
    filter_upwards [hpre, hbig.mem_nhds (R.capEuclidean_closedBall_subset hx)] with z hz hzbig
    obtain ⟨w, hw, heq⟩ := R.capEuclidean_closedBall_image.superset hz
    have hwz := R.cap_left_inverse.injOn (R.capEuclidean_closedBall_subset hw) hzbig heq
    exact hwz ▸ hw
  have hxi := mem_interior_iff_mem_nhds.mpr hnhds
  rw [interior_closedBall _ R.capEuclideanRadius_pos.ne'] at hxi
  exact mem_image_of_mem _ (hball ▸ hxi)

theorem frontier_closed_cap :
    frontier (closure (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))) =
      R.collapse '' I.neck.central_sphere := by
  rw [R.cap_boundary, frontier, frontier, closure_closure, R.interior_closed_cap]
  have hopen : IsOpen (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) := by
    rw [MetricSurgery.standard_ball_eq_euclidean g₀
      (by linarith [g₀.cylindrical_end.radius_pos])]
    exact R.cap_image_isOpen Metric.isOpen_ball
      (Metric.ball_subset_closedBall.trans R.capEuclidean_closedBall_subset)
  rw [hopen.interior_eq]

end PoincareConjecture.MetricSurgeryResult

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

theorem capChart_frontier (i : ι) :
    frontier (capChart I R U hU hd hc i).carrier =
      capInclusion I R U hU hd hc i '' ((R i).collapse '' (I i).neck.central_sphere) := by
  let f := capInclusion I R U hU hd hc i
  let C := closure ((R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4))
  have hf := capInclusion_openEmbedding I R U hU hd hc i
  have heq : f ⁻¹' frontier (f '' C) = frontier C := by
    rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous,
      preimage_image_eq _ hf.injective]
  have hsub : frontier (f '' C) ⊆ range f :=
    ((R i).isCompact_closed_cap.image hf.continuous).isClosed.frontier_subset.trans
      (image_subset_range _ _)
  have himage := congrArg (fun A => f '' A) heq
  rw [image_preimage_eq_inter_range, inter_eq_left.mpr hsub] at himage
  exact himage.trans (congrArg (fun A => f '' A) (R i).frontier_closed_cap)

theorem capChart_closure_interior (i : ι) :
    closure (interior (capChart I R U hU hd hc i).carrier) =
      (capChart I R U hU hd hc i).carrier := by
  have hf := capInclusion_openEmbedding I R U hU hd hc i
  let O := (R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)
  have hO : IsOpen O := by
    dsimp only [O]
    rw [← (R i).interior_closed_cap]
    exact isOpen_interior
  have hin : capInclusion I R U hU hd hc i '' O ⊆
      interior (capChart I R U hU hd hc i).carrier :=
    interior_maximal (image_mono subset_closure) (hf.isOpenMap O hO)
  refine Subset.antisymm
    (closure_minimal interior_subset (capChart I R U hU hd hc i).carrier_compact.isClosed) ?_
  exact (image_closure_subset_closure_image hf.continuous).trans (closure_mono hin)

end PoincareConjecture.Surgery.Terminal.Gluing
