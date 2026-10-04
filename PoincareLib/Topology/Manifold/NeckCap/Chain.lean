import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareLib.Topology.Manifold.NeckCap.Models

/-!
# Balanced neck chains and tubes

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

def EpsilonNeck.SameUpToReversal {g : RiemannianMetric 3 M}
    (N N' : EpsilonNeck g) : Prop :=
  N.epsilon = N'.epsilon ∧ N.scale = N'.scale ∧ N.center = N'.center ∧
    N.carrier = N'.carrier ∧ N.central_sphere = N'.central_sphere ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ z : RoundCylinderSpace,
          z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
            N.coordinate_map z = N'.coordinate_map (z.1, σ * z.2)

inductive ChainShape
  | finite (a b : ℤ)
  | forward (a : ℤ)
  | backward (b : ℤ)
  | biInfinite

def ChainShape.active : ChainShape → Set ℤ
  | .finite a b => Set.Icc a b
  | .forward a => Set.Ici a
  | .backward b => Set.Iic b
  | .biInfinite => Set.univ

structure BalancedNeckChain (g : RiemannianMetric 3 M) (ε : ℝ) where
  shape : ChainShape
  neck : ℤ → EpsilonNeck g
  source_necks : Set (EpsilonNeck g)
  selected : ∀ i ∈ shape.active, ∃ N ∈ source_necks,
    (neck i).SameUpToReversal N
  active_nonempty : (shape.active).Nonempty
  epsilon_eq : ∀ i ∈ shape.active, (neck i).epsilon = ε
  centers_distinct : Set.Pairwise (shape.active)
    (fun i j => (neck i).center ≠ (neck j).center)
  adjacent_overlap : ∀ i ∈ shape.active, i + 1 ∈ shape.active →
    ((neck i).carrier ∩ (neck (i + 1)).carrier).Nonempty
  overlap_contains_quarters : ∀ i ∈ shape.active, i + 1 ∈ shape.active →
    (neck i).region (ε⁻¹ / 2) ε⁻¹ ⊆ (neck (i + 1)).carrier ∧
      (neck (i + 1)).region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ (neck i).carrier
  overlap_within_three_quarters : ∀ i ∈ shape.active, i + 1 ∈ shape.active →
    (neck i).carrier ∩ (neck (i + 1)).carrier ⊆
      (neck i).region (-ε⁻¹ / 2) ε⁻¹ ∩
        (neck (i + 1)).region (-ε⁻¹) (ε⁻¹ / 2)
  later_disjoint_negative_end : ∀ i ∈ shape.active, ∀ j ∈ shape.active,
    i < j → ∃ s ∈ Set.Ioo (-ε⁻¹) 0,
      Disjoint (neck j).carrier ((neck i).region (-ε⁻¹) s)
  balanced_center_distance : ∀ i ∈ shape.active, i + 1 ∈ shape.active →
    ENNReal.ofReal ((0.99 : ℝ) * (neck i).scale * ε⁻¹) ≤
      g.edist (neck i).center (neck (i + 1)).center ∧
    g.edist (neck i).center (neck (i + 1)).center ≤
      ENNReal.ofReal ((1.01 : ℝ) * (neck i).scale * ε⁻¹)

structure EpsilonTubeCertificate (g : RiemannianMetric 3 M) (X : Set M) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_threshold : epsilon ≤ 1 / 200
  carrier : Set M
  carrier_open : IsOpen carrier
  contains_X : X ⊆ carrier
  chain : BalancedNeckChain g epsilon
  carrier_eq_chain_union : carrier = ⋃ i : {i // i ∈ chain.shape.active},
    (chain.neck i.1).carrier
  cylinder : OpenCylinderModel carrier
  central_sphere_isotopy : ∀ i ∈ chain.shape.active,
    SmoothSphereIsotopicIn carrier (chain.neck i).central_sphere cylinder.middleSphere

end PoincareMT
