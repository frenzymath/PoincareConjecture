import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.JetBounds








set_option autoImplicit false

open Set Filter Poincare.Analysis.Calculus
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

theorem eventually_derivative_bounds_of_eventually_smooth_metrics
    {n : ℕ} {U V K T : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hT : IsCompact T)
    (hKU : K ⊆ U) (hTV : T ⊆ V)
    {A B : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) U)
    (hB : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (B k) V)
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
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hA.and hB)
  have htail := tendsto_add_atTop_nat N
  have htailA : LocallyEventuallyBoundedDerivatives U (fun k ↦ A (k + N)) := by
    intro Q hQ hQU m
    obtain ⟨D, hD⟩ := hAbound Q hQ hQU m
    exact ⟨D, htail.eventually hD⟩
  have htailB : LocallyEventuallyBoundedDerivatives V (fun k ↦ B (k + N)) := by
    intro Q hQ hQV m
    obtain ⟨D, hD⟩ := hBbound Q hQ hQV m
    exact ⟨D, htail.eventually hD⟩
  obtain ⟨a, ha, hAlow⟩ := hAlow
  obtain ⟨b, hb, hBlow⟩ := hBlow
  have hbound := eventually_derivative_bounds_on_compact_domains hU hV hK hT hKU hTV
    (fun k ↦ (hN (k + N) (Nat.le_add_left N k)).1)
    (fun k ↦ (hN (k + N) (Nat.le_add_left N k)).2) htailA htailB
    (fun k ↦ hAsymm (k + N)) (fun k ↦ hBsymm (k + N))
    ⟨a, ha, htail.eventually hAlow⟩ ⟨b, hb, htail.eventually hBlow⟩
    (htail.eventually hf) (htail.eventually hmap) (htail.eventually hmetric)
  intro m
  obtain ⟨D, hD⟩ := hbound m
  obtain ⟨R, hR⟩ := eventually_atTop.mp hD
  refine ⟨D, ?_⟩
  filter_upwards [eventually_ge_atTop (R + N)] with k hk x hx
  have hNk : N ≤ k := (Nat.le_add_left N R).trans hk
  have hRk : R ≤ k - N := (Nat.le_sub_iff_add_le hNk).mpr hk
  simpa only [Nat.sub_add_cancel hNk] using hR (k - N) hRk x hx

end PoincareConjecture.CoordinateTransition
