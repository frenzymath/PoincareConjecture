import PoincareLib.Geometry.RicciFlow.MetricFamily.PullbackCoefficients

/-!
# Explicit supplier for actual-flow mixed within-jet bounds

This is the exact proposition of the unpublished lower M28 theorem
`RicciFlow.eventuallyBounded_within_pullbackCoefficients_of_spatial_bounds`.
It retains the actual flows, maps, filters and full derivative domains.
No local inhabitant or new analytic estimate is supplied.

Reference: Morgan--Tian Proposition 5.14, pp. 90-91. The pinned statement
and publication obligation are recorded in
`proof-work/tasks/M30/derivations/within-flow-jet-bounds-service.md`.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe uI uM

namespace PoincareMT.M30

/-- The unfilled lower supplier converting spatial coefficient bounds to
mixed within-jet bounds for actual Ricci flows, including tested closure
points (Morgan--Tian Proposition 5.14, pp. 90-91). -/
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

end PoincareMT.M30
