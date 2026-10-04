import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Topology.Manifold.NeckCap.Theory

/-!
# Finite oriented source-chain assembly

This module is the finite-prefix constructor after the geometric edge
producers have run.  It contains no selection or minimizer shortcut: every
source-membership, pairwise cut, and adjacent edge field is an explicit input,
while the finite chain is assembled by direct projection into the frozen
`BalancedNeckChain` structure.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

/-- The finite-list indexing used by the source-chain constructor.  Outside
the active integer interval the supplied fallback is retained only to make a
total neck function, as required by the frozen chain definition. -/
def neckOfList (l : List (EpsilonNeck g)) (fallback : EpsilonNeck g) (i : ℤ) :
    EpsilonNeck g :=
  l.getD i.toNat fallback

/-- All adjacent geometric fields needed by a balanced chain, attached to one
already oriented successor.  The two quarter inclusions are retained
separately from whole-intersection control and the metric distance bounds. -/
structure SourceEdgePacket (N Q : EpsilonNeck g) (ε : ℝ) : Prop where
  epsilon_N : N.epsilon = ε
  epsilon_Q : Q.epsilon = ε
  forward_carrier : N.region (ε⁻¹ / 2) ε⁻¹ ⊆ Q.carrier
  reciprocal_carrier : Q.region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ N.carrier
  adjacent_overlap : (N.carrier ∩ Q.carrier).Nonempty
  overlap_contains_quarters :
    N.region (ε⁻¹ / 2) ε⁻¹ ⊆ Q.carrier ∧
      Q.region (-ε⁻¹) (-ε⁻¹ / 2) ⊆ N.carrier
  overlap_within_three_quarters :
    N.carrier ∩ Q.carrier ⊆
      N.region (-ε⁻¹ / 2) ε⁻¹ ∩ Q.region (-ε⁻¹) (ε⁻¹ / 2)
  balanced_center_distance :
    ENNReal.ofReal ((0.99 : ℝ) * N.scale * ε⁻¹) ≤
        g.edist N.center Q.center ∧
      g.edist N.center Q.center ≤
        ENNReal.ofReal ((1.01 : ℝ) * N.scale * ε⁻¹)

/-- Assemble a finite oriented chain from the actual per-edge packets.  The
remaining pairwise cuts, source provenance, and common epsilon are producer
outputs; this theorem only performs the finite active-index assembly. -/
theorem exists_source_balanced_chain_of_edge_packets
    (l : List (EpsilonNeck g)) (fallback : EpsilonNeck g) (ε : ℝ)
    (hactive : (Icc (0 : ℤ) (l.length - 1)).Nonempty)
    (source_necks : Set (EpsilonNeck g))
    (hsource : ∀ i ∈ Icc (0 : ℤ) (l.length - 1),
      ∃ N ∈ source_necks,
        (neckOfList l fallback i).SameUpToReversal N)
    (heps : ∀ i ∈ Icc (0 : ℤ) (l.length - 1),
      (neckOfList l fallback i).epsilon = ε)
    (hdistinct : ∀ i ∈ Icc (0 : ℤ) (l.length - 1),
        ∀ j ∈ Icc (0 : ℤ) (l.length - 1), i ≠ j →
          (neckOfList l fallback i).center ≠
            (neckOfList l fallback j).center)
    (hedge : ∀ i ∈ Icc (0 : ℤ) (l.length - 1),
        i + 1 ∈ Icc (0 : ℤ) (l.length - 1) →
        SourceEdgePacket (neckOfList l fallback i)
          (neckOfList l fallback (i + 1)) ε)
    (hcut : ∀ i ∈ Icc (0 : ℤ) (l.length - 1),
        ∀ j ∈ Icc (0 : ℤ) (l.length - 1), i < j →
          ∃ s ∈ Ioo (-ε⁻¹) 0,
            Disjoint (neckOfList l fallback j).carrier
              ((neckOfList l fallback i).region (-ε⁻¹) s)) :
    ∃ C : BalancedNeckChain g ε, C.shape = ChainShape.finite 0 (l.length - 1) := by
  let active : Set ℤ := Icc (0 : ℤ) (l.length - 1)
  let N : ℤ → EpsilonNeck g := neckOfList l fallback
  let C : BalancedNeckChain g ε :=
    { shape := ChainShape.finite 0 (l.length - 1)
      neck := N
      source_necks := source_necks
      selected := by
        intro i hi
        exact hsource i hi
      active_nonempty := by
        simpa only [ChainShape.active] using hactive
      epsilon_eq := by
        intro i hi
        exact heps i hi
      centers_distinct := by
        intro i hi j hj hij
        exact hdistinct i hi j hj hij
      adjacent_overlap := by
        intro i hi hnext
        exact (hedge i hi hnext).adjacent_overlap
      overlap_contains_quarters := by
        intro i hi hnext
        exact (hedge i hi hnext).overlap_contains_quarters
      overlap_within_three_quarters := by
        intro i hi hnext
        exact (hedge i hi hnext).overlap_within_three_quarters
      later_disjoint_negative_end := by
        intro i hi j hj hij
        exact hcut i hi j hj hij
      balanced_center_distance := by
        intro i hi hnext
        exact (hedge i hi hnext).balanced_center_distance }
  refine ⟨C, ?_⟩
  rfl

end PoincareMT.M28
