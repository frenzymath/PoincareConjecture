import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Cap

/-!
# Connected neck and cap covers

Adapted from Mapher, `PoincareMT/Definitions/Ch09/NeckCapTopology.lean`, commit
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

structure ConnectedNeckCapCover (g : RiemannianMetric 3 M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_threshold : ℝ
  epsilon_threshold_pos : 0 < epsilon_threshold
  epsilon_threshold_le_one_two_hundred : epsilon_threshold ≤ 1 / 200
  epsilon_le_threshold : epsilon ≤ epsilon_threshold
  cap_constant : ℝ
  cap_constant_pos : 0 < cap_constant
  X : Set M
  connected_X : IsConnected X
  necks : Set (EpsilonNeck g)
  caps : Set (CapCertificate g)
  pointwise_cover : ∀ x ∈ X,
    (∃ N, N ∈ necks ∧ N.center = x) ∨
      (∃ C, C ∈ caps ∧ x ∈ C.core)
  neck_epsilon : ∀ N ∈ necks, N.epsilon = epsilon
  cap_epsilon : ∀ C ∈ caps, C.epsilon = epsilon
  cap_constant_bound : ∀ C ∈ caps, C.cap_constant ≤ cap_constant

structure NeckOnlyCover (g : RiemannianMetric 3 M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_threshold : ℝ
  epsilon_threshold_pos : 0 < epsilon_threshold
  epsilon_threshold_le_one_two_hundred : epsilon_threshold ≤ 1 / 200
  epsilon_le_threshold : epsilon ≤ epsilon_threshold
  X : Set M
  connected_X : IsConnected X
  necks : Set (EpsilonNeck g)
  pointwise_center_cover : ∀ x ∈ X, ∃ N, N ∈ necks ∧ N.center = x
  neck_epsilon : ∀ N ∈ necks, N.epsilon = epsilon

def ConnectedNeckCapCover.isWhole {g : RiemannianMetric 3 M}
    (H : ConnectedNeckCapCover g) : Prop := H.X = Set.univ

end PoincareMT
