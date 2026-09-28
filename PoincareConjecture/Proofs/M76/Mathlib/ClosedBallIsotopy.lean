import PoincareConjecture.Proofs.M76.Mathlib.ClosedExtension
import PoincareConjecture.Proofs.M76.Mathlib.SupportedAlexanderIsotopy

set_option autoImplicit false

open Set Metric
open scoped Topology

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] {R : ℝ}

noncomputable def closedBallExtension
    (e : closedBall (0 : E) R ≃ₜ closedBall (0 : E) R)
    (he : ∀ x : closedBall (0 : E) R, ‖(x : E)‖ = R → e x = x) : E ≃ₜ E :=
  e.closedExtension isClosed_closedBall fun x hx =>
    he x (by simpa only [mem_sphere, dist_zero_right] using frontier_closedBall_subset_sphere hx)

theorem closedBallExtension_apply_mem
    (e : closedBall (0 : E) R ≃ₜ closedBall (0 : E) R)
    (he : ∀ x : closedBall (0 : E) R, ‖(x : E)‖ = R → e x = x)
    {x : E} (hx : x ∈ closedBall (0 : E) R) :
    e.closedBallExtension he x = (e ⟨x, hx⟩ : E) :=
  e.closedExtension_apply_mem _ _ hx

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

noncomputable def closedBallAlexanderHomotopy
    (e : closedBall (0 : E) R ≃ₜ closedBall (0 : E) R) (hR : 0 ≤ R)
    (he : ∀ x : closedBall (0 : E) R, ‖(x : E)‖ = R → e x = x) :
    ContinuousMap.HomotopyWith (ContinuousMap.id E)
      ⟨e.closedBallExtension he, (e.closedBallExtension he).continuous⟩
      (fun f => IsHomeomorph f ∧ ∀ x, R ≤ ‖x‖ → f x = x) :=
  (e.closedBallExtension he).supportedAlexanderHomotopy hR
    (e.closedBallExtension_fixed_outside he)

end Homeomorph
