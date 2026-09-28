import PoincareConjecture.Statements.M64Comparison







set_option autoImplicit false

universe u

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture




theorem m64ComparisonTheory_of_fields
    (hintrinsic : M64IntrinsicAnnulusComparison)
    (hstatic : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [SecondCountableTopology M] [ChartedSpace LoopAmbient M]
      [IsManifold (𝓡 3) ∞ M]
      (g : RiemannianMetric 3 M) (D : LeviCivitaData g),
      IsCompact (Set.univ : Set M) → M64StaticApproximationTheory g D)
    (hflow : ∀ (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
      [SecondCountableTopology M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold (𝓡 n) ∞ M]
      (a b : ℝ) (F : RicciFlow n M (Set.Icc a b)),
      3 ≤ n → IsCompact (Set.univ : Set M) →
        Nonempty (M64FlowConclusion F))
    (hthree : ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
      [SecondCountableTopology M] [ChartedSpace LoopAmbient M]
      [IsManifold (𝓡 3) ∞ M]
      (a b : ℝ) (F : RicciFlow 3 M (Set.Icc a b)),
      IsCompact (Set.univ : Set M) →
        Nonempty (M64ThreeDimensionalFlowConclusion F)) :
    M64ComparisonTheory.{u} := by
  exact ⟨hintrinsic, hstatic, hflow, hthree⟩

end PoincareConjecture
