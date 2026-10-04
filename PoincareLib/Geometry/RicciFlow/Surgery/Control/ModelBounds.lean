import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry

/-!
Adapted from Mapher `PoincareMT/Definitions/M45ModelAnalytics.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M45 primitive analytic estimates for geometric models

These are supporting conclusions of M45, derived from Morgan--Tian
Definition 2.16, Eq. (2.1), p. 30, and Definitions 2.18 and 9.76,
pp. 31 and 231. Four intrinsic spatial metric jets control the displayed
gradient and absolute spatial evolution expression. The round case uses
the quantitative positive scalar lower bound after normalization.
See `reviews/contracts/2026-09-15-model-analytic-margin-round1.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- Primitive scalar, gradient and absolute spatial evolution bounds at x.
The last expression becomes the scalar time derivative under Ricci flow. -/
def M45PointwiseAnalyticEstimate
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (x : M) (B : ℝ) : Prop :=
  0 < D.scalarCurvature x ∧
    scalarGradientNorm g D x ≤ B * D.scalarCurvature x ^ (3 / 2 : ℝ) ∧
    |D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x| ≤
      B * D.scalarCurvature x ^ 2

/-- Universal model bounds, chosen before every actual metric and certificate.
No estimate on an arbitrary canonical component or surgery flow is asserted. -/
structure M45ModelAnalyticBounds where
  neck_constant : ℝ
  neck_constant_pos : 0 < neck_constant
  round_constant : ℝ
  round_constant_pos : 0 < round_constant
  neck :
    ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M],
      ∀ (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (N : EpsilonNeck g),
        N.epsilon ≤ 1 / 200 →
        M45PointwiseAnalyticEstimate g D N.center neck_constant
  round :
    ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M],
      ∀ (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (epsilon : ℝ)
        (N : SingularRoundComponent g epsilon),
        epsilon ≤ 1 / 200 → ∀ x ∈ N.carrier,
          M45PointwiseAnalyticEstimate g D x round_constant
  /-- Explicit Type-0 application at normalized time zero. Four spatial
      jets suffice even when the supplied interval is a singleton. -/
  standard_neck :
    ∀ (atlas : StandardCylinderAtlas) {g₀ : StandardInitialMetric}
      (F : MaximalStandardCapFlow g₀) (t epsilon : ℝ) (x : StandardCapSpace)
      (I : Set ℝ),
      StandardEvolvingNeck atlas F t epsilon x I →
      epsilon ≤ 1 / 200 → 0 ∈ I →
      M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x neck_constant

end PoincareMT
