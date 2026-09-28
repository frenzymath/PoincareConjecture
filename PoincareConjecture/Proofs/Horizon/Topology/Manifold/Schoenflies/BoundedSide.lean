import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallExterior
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.DomainIdentification












set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [ProperSpace E] [Nontrivial E]

omit [Nontrivial E] in

theorem closure_image_ball (e : OpenPartialHomeomorph E E)
    (hs : closedBall (0 : E) 1 ⊆ e.source) :
    closure (e '' ball (0 : E) 1) = e '' closedBall (0 : E) 1 := by
  have hK : IsCompact (e '' closedBall (0 : E) 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn (e.continuousOn.mono hs)
  refine Subset.antisymm (closure_minimal (image_mono ball_subset_closedBall) hK.isClosed) ?_
  have hf : ContinuousOn e (closure (ball (0 : E) 1)) := by
    rw [closure_ball (0 : E) (by norm_num : (1 : Real) ≠ 0)]
    exact e.continuousOn.mono hs
  simpa only [closure_ball (0 : E) (by norm_num : (1 : Real) ≠ 0)] using hf.image_closure



theorem image_closedBall_eq_closure_of_boundary
    (e : OpenPartialHomeomorph E E) (hdim : 1 < Module.rank Real E)
    (hs : closedBall (0 : E) 1 ⊆ e.source)
    {Omega : Set E} (hOmega : IsOpen Omega) (hconn : IsConnected Omega)
    (hbounded : Bornology.IsBounded Omega)
    (hfront : e '' sphere (0 : E) 1 = frontier Omega) :
    e '' closedBall (0 : E) 1 = closure Omega := by
  let K := e '' closedBall (0 : E) 1
  have hK : IsCompact K :=
    (isCompact_closedBall 0 1).image_of_continuousOn (e.continuousOn.mono hs)
  have hinner : e '' ball (0 : E) 1 = interior K := e.image_ball_eq_interior hs rfl
  have hfront' : frontier Omega = frontier K :=
    hfront.symm.trans (e.image_sphere_eq_frontier hs rfl)
  have hinnerConn : IsPreconnected (interior K) := by
    rw [← hinner]
    exact (convex_ball (0 : E) 1).isPreconnected.image e
      (e.continuousOn.mono (ball_subset_closedBall.trans hs))
  have houterConn : IsConnected Kᶜ := e.isConnected_compl_image_closedBall hdim hs
  have houterUnbounded : ¬Bornology.IsBounded Kᶜ := by
    intro h
    apply NormedSpace.unbounded_univ Real E
    simpa only [union_compl_self] using hK.isBounded.union h
  have hcover : interior K ∪ Kᶜ = (frontier K)ᶜ := by
    rw [compl_frontier_eq_union_interior, hK.isClosed.isOpen_compl.interior_eq]
  have hOmegaInner : Omega = interior K :=
    Poincare.Topology.eq_bounded_side_of_frontier_partition hOmega hconn hbounded hfront'
      isOpen_interior hK.isClosed.isOpen_compl hinnerConn houterConn.isPreconnected
      (disjoint_left.mpr fun x hx hx' => hx' (interior_subset hx)) hcover houterUnbounded
  rw [hOmegaInner, ← hinner]
  exact (e.closure_image_ball hs).symm

end OpenPartialHomeomorph
