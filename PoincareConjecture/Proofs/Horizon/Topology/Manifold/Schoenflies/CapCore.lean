import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Neighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallImages
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Core.BoundarySphere













set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)



theorem exists_euclidean_closed_core_ball_neighborhood
    (hkind : C.model_kind = .euclidean) :
    ∃ b : OpenPartialHomeomorph (EuclideanSpace Real (Fin 3)) M,
      Metric.closedBall 0 1 ⊆ b.source ∧
      C.closed_core ⊆ b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 = C.closed_core ∧
      b '' Metric.ball 0 1 = C.core ∧
      b '' Metric.sphere 0 1 = C.boundary_sphere := by
  obtain ⟨e, hs, ht, he, hei, ⟨D⟩, hclosure, hf, hfront⟩ :=
    C.exists_euclidean_core_boundary_coordinates hkind
  obtain ⟨b, hbsource, hbtarget, hb, hbi, hbimage⟩ :=
    D.exists_ball_neighborhood
      (fun p : UnitTwoSphere => e (C.boundary_neck.coordinate_map (p, 0))) hf hfront
  have hcore : C.closed_core ⊆ e.source := hs.symm ▸ C.closed_core_subset_carrier
  let c := b.trans e.symm
  have hcsource : Metric.closedBall 0 1 ⊆ c.source := by
    intro x hx
    refine ⟨hbsource hx, ?_⟩
    change b x ∈ e.target
    rw [ht]
    exact mem_univ _
  have hcimage : c '' Metric.closedBall 0 1 = C.closed_core := by
    change (e.symm ∘ b) '' Metric.closedBall 0 1 = C.closed_core
    calc
      (e.symm ∘ b) '' Metric.closedBall 0 1 =
          e.symm '' (b '' Metric.closedBall 0 1) :=
        (Set.image_image (⇑e.symm) (⇑b) (Metric.closedBall 0 1)).symm
      _ = e.symm '' (e '' C.closed_core) := by rw [hbimage, hclosure]
      _ = C.closed_core := e.toPartialEquiv.symm_image_image_of_subset_source hcore
  refine ⟨c, hcsource, ?_, ?_, ?_, hcimage, ?_, ?_⟩
  · intro x hx
    exact ⟨hcore hx, hbtarget (hclosure.symm ▸ mem_image_of_mem e hx)⟩
  · exact hei.comp (hb.mono (fun x hx => hx.1)) (fun x hx => hx.2)
  · exact hbi.comp (he.mono (fun x hx => hx.1)) (fun x hx => hx.2)
  · rw [c.image_ball_eq_interior hcsource hcimage, ← C.core_eq_interior_closed_core]
  · rw [c.image_sphere_eq_frontier hcsource hcimage,
      C.closed_core_compact.isClosed.frontier_eq, ← C.core_eq_interior_closed_core,
      ← C.boundary_eq_closed_core_diff_core]

end PoincareConjecture.CapCertificate
