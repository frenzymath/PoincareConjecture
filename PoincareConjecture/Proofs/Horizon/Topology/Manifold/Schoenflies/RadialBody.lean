import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.RadialBody.Parametrization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BoundedSide
import Mathlib.Analysis.InnerProductSpace.PiL2










set_option autoImplicit false

open Set Metric

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [ProperSpace E] [Nontrivial E]



theorem image_closedBall_eq_of_image_sphere_eq
    (F H : E ≃ₜ E) (hdim : 1 < Module.rank Real E)
    (hboundary : F '' sphere (0 : E) 1 = H '' sphere (0 : E) 1) :
    F '' closedBall (0 : E) 1 = H '' closedBall (0 : E) 1 := by
  have hfront : F '' sphere (0 : E) 1 = frontier (H '' ball (0 : E) 1) := by
    rw [← H.image_frontier, frontier_ball (0 : E) (by norm_num : (1 : Real) ≠ 0)]
    exact hboundary
  have hconn : IsConnected (H '' ball (0 : E) 1) :=
    ((convex_ball (0 : E) 1).isConnected (by simp)).image H H.continuous.continuousOn
  have hbounded : Bornology.IsBounded (H '' ball (0 : E) 1) :=
    ((isCompact_closedBall (0 : E) 1).image H.continuous).isBounded.subset
      (image_mono ball_subset_closedBall)
  have h := F.toOpenPartialHomeomorph.image_closedBall_eq_closure_of_boundary hdim
    (by simp) (H.isOpenMap _ isOpen_ball) hconn hbounded hfront
  rw [← H.image_closure, closure_ball (0 : E) (by norm_num : (1 : Real) ≠ 0)] at h
  exact h


theorem image_ball_eq_of_image_sphere_eq
    (F H : E ≃ₜ E) (hdim : 1 < Module.rank Real E)
    (hboundary : F '' sphere (0 : E) 1 = H '' sphere (0 : E) 1) :
    F '' ball (0 : E) 1 = H '' ball (0 : E) 1 := by
  have h := congrArg interior (F.image_closedBall_eq_of_image_sphere_eq H hdim hboundary)
  simpa only [← F.image_interior, ← H.image_interior,
    interior_closedBall (0 : E) (by norm_num : (1 : Real) ≠ 0)] using h



theorem image_closedBall_eq_radialBody
    (F : E ≃ₜ E) (hdim : 1 < Module.rank Real E)
    (r : sphere (0 : E) 1 → Real) (hr : Continuous r) (hpos : ∀ p, 0 < r p)
    (hboundary : F '' sphere (0 : E) 1 =
      range (fun p : sphere (0 : E) 1 => r p • (p : E))) :
    F '' closedBall (0 : E) 1 = Poincare.Topology.radialClosedBody r := by
  rw [← Poincare.Topology.radialHomeomorph_image_closedBall r hr hpos]
  apply F.image_closedBall_eq_of_image_sphere_eq _ hdim
  rw [Poincare.Topology.radialHomeomorph_image_sphere]
  exact hboundary


theorem image_ball_eq_radialBody
    (F : E ≃ₜ E) (hdim : 1 < Module.rank Real E)
    (r : sphere (0 : E) 1 → Real) (hr : Continuous r) (hpos : ∀ p, 0 < r p)
    (hboundary : F '' sphere (0 : E) 1 =
      range (fun p : sphere (0 : E) 1 => r p • (p : E))) :
    F '' ball (0 : E) 1 = Poincare.Topology.radialOpenBody r := by
  rw [← Poincare.Topology.radialHomeomorph_image_ball r hr hpos]
  apply F.image_ball_eq_of_image_sphere_eq _ hdim
  rw [Poincare.Topology.radialHomeomorph_image_sphere]
  exact hboundary

end Homeomorph

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem image_balls_eq_radialBodies (F : E3 ≃ₜ E3)
    (r : S2 → Real) (hr : Continuous r) (hpos : ∀ p, 0 < r p)
    (hboundary : F '' sphere (0 : E3) 1 = range (fun p : S2 => r p • (p : E3))) :
    F '' closedBall (0 : E3) 1 = Poincare.Topology.radialClosedBody r ∧
      F '' ball (0 : E3) 1 = Poincare.Topology.radialOpenBody r := by
  have hdim : 1 < Module.rank Real E3 := by
    rw [← Module.finrank_eq_rank]
    norm_num
  exact ⟨F.image_closedBall_eq_radialBody hdim r hr hpos hboundary,
    F.image_ball_eq_radialBody hdim r hr hpos hboundary⟩

end Poincare.Manifold.Schoenflies
