import PoincareConjecture.Definitions.M25NeckCapTopology
import PoincareConjecture.Statements.Ch09.NeckCapTopology

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedNeckCapTopologyTheory where
  epsilon₀ : ℝ
  epsilon₀_pos : 0 < epsilon₀
  epsilon₀_le_one_two_hundred : epsilon₀ ≤ 1 / 200

  a19 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : NeckOnlyCover g, H.epsilon ≤ epsilon₀ →
        ∀ hsep, AppendixA19Theory g H hsep

  a20 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : NeckOnlyCover g, H.epsilon ≤ epsilon₀ →
        ∀ hwhole : H.X = Set.univ, AppendixA20Theory g H hwhole

  a21 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ epsilon₀ →
        Nonempty (RepairedNeckCapTopologyData g H)

  a25 : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M],
    ∀ g : RiemannianMetric 3 M,
      ∀ H : ConnectedNeckCapCover g, H.epsilon ≤ epsilon₀ → H.isWhole →
        Nonempty (GlobalNeckCapConclusion g H.epsilon H.cap_constant)

end PoincareConjecture
