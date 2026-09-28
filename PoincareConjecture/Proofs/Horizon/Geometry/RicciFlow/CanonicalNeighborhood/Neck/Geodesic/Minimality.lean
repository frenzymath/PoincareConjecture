import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Distance

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.EpsilonNeck

theorem intrinsic_minimality_to_axial_competitor
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (U : Set M)
    {x : ℝ → M} {f : ℝ → ℝ} {L r ε C : ℝ}
    (hr : 0 ≤ r) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hsegment : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      a ≤ b → ENNReal.ofReal (b - a) ≤
        intrinsicEDist g U (x a) (x b))
    (hcompetitor : ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      a ≤ b → intrinsicEDist g U (x a) (x b) ≤
        ENNReal.ofReal (r * Real.sqrt (1 + ε) *
          (|f b - f a| + C))) :
    ∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
      a ≤ b → b - a ≤ r * Real.sqrt (1 + ε) * (|f b - f a| + C) := by
  intro a ha b hb hab
  have hright : 0 ≤ r * Real.sqrt (1 + ε) * (|f b - f a| + C) := by
    positivity
  have hle := (hsegment a ha b hb hab).trans (hcompetitor a ha b hb hab)
  exact (ENNReal.ofReal_le_ofReal_iff hright).mp hle

end PoincareConjecture.EpsilonNeck
