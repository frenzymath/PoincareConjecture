import PoincareConjecture.Proofs.M60.Mathlib.ExponentialComparison
import PoincareConjecture.Statements.M60Area










set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem m60FixedMapAreaProperties_of_variation
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (D : ℝ)
    (f : UnitTwoSphere → M)
    (htrace : ∀ t ∈ Set.Icc a b,
      Integrable (m60SphereRicciTraceDensity (F.connection t) f) volume)
    (hvariation : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun s => m60SphereArea (F.metric s) f)
        (-(∫ z : LoopPlane, m60SphereRicciTraceDensity (F.connection t) f z ∂volume))
        (Set.Icc a b) t)
    (hbound : ∀ t ∈ Set.Icc a b,
      |-(∫ z : LoopPlane, m60SphereRicciTraceDensity (F.connection t) f z ∂volume)| ≤
        4 * D * m60SphereArea (F.metric t) f) :
    M60FixedMapAreaProperties F D f where
  continuous := fun t ht => (hvariation t ht).continuousWithinAt
  ricci_trace_integrable := htrace
  variation := hvariation
  absolute_derivative_bound := hbound
  integrating_factor := by
    simpa only [neg_mul] using M60.antitoneOn_exp_mul_of_deriv_le hvariation
      (fun t ht => (abs_le.mp (hbound t ht)).2) a
  exponential_comparison := fun _ hs _ ht hst =>
    M60.le_exp_mul_of_deriv_le hvariation (fun t ht => (abs_le.mp (hbound t ht)).2)
      hs ht hst
  two_sided_comparison := fun _ hs _ ht =>
    M60.le_exp_abs_mul_of_abs_deriv_le hvariation hbound hs ht

end PoincareConjecture
