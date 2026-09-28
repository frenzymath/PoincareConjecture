import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.ComparisonAngle
import Mathlib.Topology.MetricSpace.Basic









set_option autoImplicit false

namespace Poincare.Alexandrov



def ComparisonAnglePackingBound (X : Type*) [MetricSpace X] (α : ℝ) (N : ℕ) : Prop :=
  ∀ (k : ℕ) (p : X) (q : Fin k → X),
    (∀ i, q i ≠ p) →
    (∀ i j, i ≠ j →
      α < comparisonAngle (dist p (q i)) (dist p (q j)) (dist (q i) (q j))) →
    k ≤ N


theorem ComparisonAnglePackingBound.of_isometry
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {α : ℝ} {N : ℕ}
    (hY : ComparisonAnglePackingBound Y α N) {f : X → Y} (hf : Isometry f) :
    ComparisonAnglePackingBound X α N := by
  intro k p q hq hangle
  apply hY k (f p) (f ∘ q)
  · intro i
    exact hf.injective.ne (hq i)
  · intro i j hij
    simpa only [Function.comp_apply, hf.dist_eq] using hangle i j hij

end Poincare.Alexandrov
