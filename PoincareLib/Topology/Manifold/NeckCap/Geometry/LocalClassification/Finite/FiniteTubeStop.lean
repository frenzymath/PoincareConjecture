import PoincareLib.Topology.Manifold.NeckCap.Geometry.Fibration.Intrinsic.IntrinsicChainTube

/-!
# The finite-chain stopping branch

When a finite chain has no frontier point in a preconnected target set, the
target lies in the chain union.  This is the relative topological step needed
before the existing finite-chain tube constructor can be applied in A.21
Case II.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.BalancedNeckChain

/-- A preconnected set meeting a finite chain and avoiding its frontier is
contained in the chain union, so the intrinsic finite-chain constructor gives
an actual tube containing it. -/
theorem exists_epsilonTubeCertificate_of_preconnected_frontier_disjoint :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) (X : Set M) {a b : ℤ},
      C.shape = ChainShape.finite a b → epsilon ≤ epsilon0 →
      IsPreconnected X →
      (X ∩ (⋃ i ∈ C.shape.active, (C.neck i).carrier)).Nonempty →
      Disjoint X (frontier (⋃ i ∈ C.shape.active, (C.neck i).carrier)) →
      ∃ T : EpsilonTubeCertificate g X,
        T.epsilon = epsilon ∧ HEq T.chain C ∧
        T.carrier = ⋃ i ∈ C.shape.active, (C.neck i).carrier := by
  obtain ⟨epsilon0, hpos, hcap, hfinite⟩ :=
    BalancedNeckChain.exists_epsilonTubeCertificate_of_finite.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C X a b hshape hepsilon hX hmeet hfront
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  have hUopen : IsOpen U := by
    exact isOpen_iUnion fun i => isOpen_iUnion fun _ => (C.neck i).carrier_open
  have hXsub : X ⊆ U := by
    apply hX.subset_of_closure_inter_subset hUopen hmeet
    intro z hz
    by_contra hzU
    have hzfront : z ∈ frontier U := by
      rw [hUopen.frontier_eq]
      exact ⟨hz.1, hzU⟩
    exact (Set.disjoint_left.1 hfront) hz.2 hzfront
  obtain ⟨T, hε, hchain, hcarrier⟩ :=
    hfinite C X hshape hepsilon hXsub
  refine ⟨T, hε, hchain, ?_⟩
  simpa only [U] using hcarrier

end PoincareMT.BalancedNeckChain
