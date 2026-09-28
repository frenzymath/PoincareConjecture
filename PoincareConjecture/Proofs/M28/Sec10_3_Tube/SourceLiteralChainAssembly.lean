import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceBalancedChainAssembly

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem exists_literal_source_balanced_chain_of_edge_packets
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
    ∃ C : BalancedNeckChain g ε,
      C.shape = ChainShape.finite 0 (l.length - 1) ∧
        C.neck = neckOfList l fallback ∧ C.source_necks = source_necks := by
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
  exact ⟨C, rfl, rfl, rfl⟩

end PoincareConjecture.M28
