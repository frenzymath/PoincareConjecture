import PoincareLib.Topology.Manifold.Surgery.Event.Open.OpenPointMotion
import PoincareLib.Topology.Manifold.Surgery.Event.Punctured.PuncturedComponent
import PoincareLib.Topology.Manifold.Surgery.Event.Component.ComponentBalls

/-!
# Placing two actual centers in one original ball chart

The punctured center component admits ambient point motions fixing its
exterior. The original ball inverse distinguishes a nonzero target
coordinate from the first center. The resulting diffeomorphism places
the second center in that chart and keeps the first center fixed.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)

/-- A nonzero valid original coordinate is distinct from the actual ball center. -/
theorem surgeryBall_map_ne_center (v : StandardCapSpace)
    (hv : v ∈ Metric.ball 0 2) (hv0 : v ≠ 0) : B.map v ≠ B.map 0 := by
  intro heq
  have hcoord := congrArg B.inverse heq
  rw [B.left_inverse hv, B.left_inverse (by simp)] at hcoord
  exact hv0 hcoord

/-- Move a second point in the same actual component to a prescribed
nonzero coordinate of the first ball. The first center and every point
outside that component are fixed by the same smooth diffeomorphism. -/
theorem exists_second_center_in_ball
    (q : A.carrier) (hq : q ∈ connectedComponent (B.map 0)) (hq0 : q ≠ B.map 0)
    (v : StandardCapSpace) (hv : v ∈ Metric.ball 0 2) (hv0 : v ≠ 0) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
      e (B.map 0) = B.map 0 ∧ e q = B.map v ∧
        ∀ x : A.carrier, x ∉ connectedComponent (B.map 0) → e x = x := by
  let O : Set A.carrier := connectedComponent (B.map 0) \ {B.map 0}
  have hopen : IsOpen (connectedComponent (B.map 0)) := (componentOpen A (B.map 0)).isOpen
  have hO : IsOpen O := IsOpen.sdiff hopen isClosed_singleton
  have hconn : IsPreconnected O := punctured_component_preconnected A (B.map 0)
  have hqO : q ∈ O := ⟨hq, hq0⟩
  have hvO : B.map v ∈ O :=
    ⟨surgeryBall_image_subset_center_component B (Set.mem_image_of_mem B.map hv),
      surgeryBall_map_ne_center B v hv hv0⟩
  obtain ⟨e, he, hfix⟩ :=
    exists_diffeomorph_in_connected_open hO hconn q hqO (B.map v) hvO
  refine ⟨e, hfix _ (fun h => h.2 rfl), he, ?_⟩
  intro x hx
  exact hfix x (fun h => hx h.1)

/-- Applied to two actual ball centers, the same motion keeps their
literal images and fixes the exterior of their common original component. -/
theorem exists_two_ball_centers_in_chart (D : SurgeryBallEmbedding A)
    (hD : D.map 0 ∈ connectedComponent (B.map 0)) (hne : D.map 0 ≠ B.map 0)
    (v : StandardCapSpace) (hv : v ∈ Metric.ball 0 2) (hv0 : v ≠ 0) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
      e (B.map 0) = B.map 0 ∧ e (D.map 0) = B.map v ∧
        ∀ x : A.carrier, x ∉ connectedComponent (B.map 0) → e x = x :=
  exists_second_center_in_ball B (D.map 0) hD hne v hv hv0

end PoincareMT.M38
