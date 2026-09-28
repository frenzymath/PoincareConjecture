import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients














set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe uI uM

namespace PoincareConjecture.M30




def WithinFlowJetBoundsService : Prop :=
  ∀ {n : ℕ} {α : Type uI} {M : α → Type uM}
    [∀ w, TopologicalSpace (M w)]
    [∀ w, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M w)]
    [∀ w, IsManifold (𝓡 n) ∞ (M w)]
    (l : Filter α) (J : α → Set ℝ) (F : ∀ w, RicciFlow n (M w) (J w))
    (U : α → Set (EuclideanSpace ℝ (Fin n)))
    (e : ∀ w, EuclideanSpace ℝ (Fin n) → M w)
    (T S : α → Set (ℝ × EuclideanSpace ℝ (Fin n))),
    (∀ w, UniqueDiffOn ℝ (J w)) →
    (∀ w, IsOpen (U w)) →
    (∀ w, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e w) (U w)) →
    (∀ w y, y ∈ U w → (mfderiv (𝓡 n) (𝓡 n) (e w) y).IsInvertible) →
    (∀ w, T w ⊆ interior (J w) ×ˢ U w) →
    (∀ w, S w ⊆ (J w ×ˢ U w) ∩ closure (T w)) →
    (∀ q, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in l, ∀ z ∈ T w, ∀ j ≤ q,
      ‖iteratedFDeriv ℝ j ((F w).metric z.1 |>.pullbackCoefficients (e w)) z.2‖ ≤ B) →
    ∀ {a : ℝ}, 0 < a →
    (∀ᶠ w in l, ∀ z ∈ T w, ∀ v,
      a * ‖v‖ ^ 2 ≤ ((F w).metric z.1).pullbackCoefficients (e w) z.2 v v) →
    ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in l, ∀ z ∈ S w,
      ‖iteratedFDerivWithin ℝ m
        (fun z => ((F w).metric z.1).pullbackCoefficients (e w) z.2)
        (J w ×ˢ U w) z‖ ≤ B

end PoincareConjecture.M30
