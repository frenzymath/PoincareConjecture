import PoincareConjecture.Definitions.Ch12.StandardCap

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

def M45PointwiseAnalyticEstimate
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (x : M) (B : ℝ) : Prop :=
  0 < D.scalarCurvature x ∧
    scalarGradientNorm g D x ≤ B * D.scalarCurvature x ^ (3 / 2 : ℝ) ∧
    |D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x| ≤
      B * D.scalarCurvature x ^ 2

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

  standard_neck :
    ∀ (atlas : StandardCylinderAtlas) {g₀ : StandardInitialMetric}
      (F : MaximalStandardCapFlow g₀) (t epsilon : ℝ) (x : StandardCapSpace)
      (I : Set ℝ),
      StandardEvolvingNeck atlas F t epsilon x I →
      epsilon ≤ 1 / 200 → 0 ∈ I →
      M45PointwiseAnalyticEstimate (F.metric t) (F.connection t) x neck_constant

end PoincareConjecture
