import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.CurvedCapSeparation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallMatching.NestingCriteria

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem disjoint_closed_cap_boundaries
    {v : E3} {b : Real} {E F Δ Λ : Set E3}
    (hEF : Disjoint E F) (hΔΛ : Disjoint Δ Λ)
    (hE : ∀ y ∈ E, inner Real v y ≤ b)
    (hF : ∀ y ∈ F, inner Real v y ≤ b)
    (hΔ : ∀ y ∈ Δ, b ≤ inner Real v y)
    (hΛ : ∀ y ∈ Λ, b ≤ inner Real v y)
    (hΔrim : ∀ y ∈ Δ, inner Real v y = b → y ∈ E)
    (hΛrim : ∀ y ∈ Λ, inner Real v y = b → y ∈ F) :
    Disjoint (E ∪ Δ) (F ∪ Λ) := by
  apply disjoint_left.mpr
  rintro y (hyE | hyΔ) (hyF | hyΛ)
  · exact disjoint_left.mp hEF hyE hyF
  · exact disjoint_left.mp hEF hyE
      (hΛrim y hyΛ (le_antisymm (hE y hyE) (hΛ y hyΛ)))
  · exact disjoint_left.mp hEF
      (hΔrim y hyΔ (le_antisymm (hF y hyF) (hΔ y hyΔ))) hyF
  · exact disjoint_left.mp hΔΛ hyΔ hyΛ

theorem closing_ball_subset_of_one_interior_point
    {v : E3} {b : Real} {E F Δ Λ : Set E3}
    (A B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hA : A '' sphere (0 : E3) 1 = E ∪ Δ)
    (hB : B '' sphere (0 : E3) 1 = F ∪ Λ)
    (hEF : Disjoint E F) (hΔΛ : Disjoint Δ Λ)
    (hE : ∀ y ∈ E, inner Real v y ≤ b)
    (hF : ∀ y ∈ F, inner Real v y ≤ b)
    (hΔ : ∀ y ∈ Δ, b ≤ inner Real v y)
    (hΛ : ∀ y ∈ Λ, b ≤ inner Real v y)
    (hΔrim : ∀ y ∈ Δ, inner Real v y = b → y ∈ E)
    (hΛrim : ∀ y ∈ Λ, inner Real v y = b → y ∈ F)
    {p : E3} (hpΔ : p ∈ Δ) (hpB : p ∈ B '' ball (0 : E3) 1) :
    A '' closedBall (0 : E3) 1 ⊆ B '' ball (0 : E3) 1 := by
  apply closedBall_image_subset_openBall_of_disjoint_boundaries A.toHomeomorph B.toHomeomorph
  · change Disjoint (A '' sphere (0 : E3) 1) (B '' sphere (0 : E3) 1)
    rw [hA, hB]
    exact disjoint_closed_cap_boundaries hEF hΔΛ hE hF hΔ hΛ hΔrim hΛrim
  · change p ∈ A '' sphere (0 : E3) 1
    rw [hA]
    exact Or.inr hpΔ
  · exact hpB

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
