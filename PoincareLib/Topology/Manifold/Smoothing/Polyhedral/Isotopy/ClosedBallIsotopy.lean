import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.ClosedExtension
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Isotopy.SupportedAlexanderIsotopy

/-!
# Extending and isotoping a boundary-fixed ball homeomorphism

Extend a homeomorphism of a closed ball by the identity, assuming it fixes
the bounding sphere. Its Alexander homotopy consists of homeomorphisms and
fixes that sphere and its exterior throughout. This is the ball step of
Hamilton 1976, proof of Theorem 1, pp. 66, 68. See M76 derivation 10.
-/

set_option autoImplicit false

open Set Metric
open scoped Topology

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] {R : ℝ}

/-- A sphere-fixed homeomorphism of a closed ball extends by the identity
to its ambient space. The frontier need only be contained in the sphere;
see Hamilton pp. 66, 68 and M76 derivation 10. -/
noncomputable def closedBallExtension
    (e : closedBall (0 : E) R ≃ₜ closedBall (0 : E) R)
    (he : ∀ x : closedBall (0 : E) R, ‖(x : E)‖ = R → e x = x) : E ≃ₜ E :=
  e.closedExtension isClosed_closedBall fun x hx =>
    he x (by simpa only [mem_sphere, dist_zero_right] using frontier_closedBall_subset_sphere hx)

/-- The ball extension agrees with the original homeomorphism on the ball.
See M76 derivation 10. -/
theorem closedBallExtension_apply_mem
    (e : closedBall (0 : E) R ≃ₜ closedBall (0 : E) R)
    (he : ∀ x : closedBall (0 : E) R, ‖(x : E)‖ = R → e x = x)
    {x : E} (hx : x ∈ closedBall (0 : E) R) :
    e.closedBallExtension he x = (e ⟨x, hx⟩ : E) :=
  e.closedExtension_apply_mem _ _ hx

/-- The ball extension fixes the sphere and its exterior, including the
degenerate radius-zero case. See M76 derivation 10. -/
theorem closedBallExtension_fixed_outside
    (e : closedBall (0 : E) R ≃ₜ closedBall (0 : E) R)
    (he : ∀ x : closedBall (0 : E) R, ‖(x : E)‖ = R → e x = x)
    (x : E) (hx : R ≤ ‖x‖) :
    e.closedBallExtension he x = x := by
  by_cases hxB : x ∈ closedBall (0 : E) R
  · rw [e.closedBallExtension_apply_mem he hxB]
    have hnorm : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hxB
    exact congrArg Subtype.val (he ⟨x, hxB⟩ (le_antisymm hnorm hx))
  · exact e.closedExtension_apply_notMem _ _ hxB

variable [NormedSpace ℝ E]

/-- A boundary-fixed ball homeomorphism extends to a homotopy from the
ambient identity through homeomorphisms fixing the sphere and exterior.
The inverse family is jointly continuous by `continuous_alexanderFamily_symm`.
See Hamilton pp. 66, 68 and M76 derivation 10. -/
noncomputable def closedBallAlexanderHomotopy
    (e : closedBall (0 : E) R ≃ₜ closedBall (0 : E) R) (hR : 0 ≤ R)
    (he : ∀ x : closedBall (0 : E) R, ‖(x : E)‖ = R → e x = x) :
    ContinuousMap.HomotopyWith (ContinuousMap.id E)
      ⟨e.closedBallExtension he, (e.closedBallExtension he).continuous⟩
      (fun f => IsHomeomorph f ∧ ∀ x, R ≤ ‖x‖ → f x = x) :=
  (e.closedBallExtension he).supportedAlexanderHomotopy hR
    (e.closedBallExtension_fixed_outside he)

end Homeomorph
