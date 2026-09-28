import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.JetBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Poincare.Analysis.Calculus
open scoped Topology NNReal Manifold ContDiff

namespace PoincareConjecture.M47

theorem terminalCommonInterval_transition_jet_bounds
    {n : ℕ} {U V K T : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hT : IsCompact T)
    (hKU : K ⊆ U) (hTV : T ⊆ V)
    {A B : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ∀ k, ContDiffOn ℝ ∞ (A k) U) (hB : ∀ k, ContDiffOn ℝ ∞ (B k) V)
    (hAbound : LocallyEventuallyBoundedDerivatives U A)
    (hBbound : LocallyEventuallyBoundedDerivatives V B)
    (hAsymm : ∀ k x, x ∈ U → ∀ v w, A k x v w = A k x w v)
    (hBsymm : ∀ k x, x ∈ V → ∀ v w, B k x v w = B k x w v)
    (hAlow : ∃ a : ℝ, 0 < a ∧ ∀ᶠ k in atTop,
      ∀ x ∈ K, ∀ v, a * ‖v‖ ^ 2 ≤ A k x v v)
    (hBlow : ∃ b : ℝ, 0 < b ∧ ∀ᶠ k in atTop,
      ∀ x ∈ T, ∀ v, b * ‖v‖ ^ 2 ≤ B k x v v)
    (hf : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) (interior K))
    (hmap : ∀ᶠ k in atTop, MapsTo (f k) (interior K) (interior T))
    (hmetric : ∀ᶠ k in atTop, ∀ x ∈ interior K, ∀ v w,
      B k (f k x) (fderiv ℝ (f k) x v) (fderiv ℝ (f k) x w) = A k x v w) :
    ∀ m : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop, ∀ x ∈ interior K,
      ‖iteratedFDeriv ℝ m (f k) x‖ ≤ C := by
  exact CoordinateTransition.eventually_derivative_bounds_on_compact_domains
    hU hV hK hT hKU hTV hA hB hAbound hBbound hAsymm hBsymm hAlow hBlow hf hmap hmetric

end PoincareConjecture.M47
