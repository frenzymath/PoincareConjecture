import PoincareConjecture.Statements.M64Comparison
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.ProjectionComplete








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture




theorem m64ProjectionField_of_annulus
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}
    (G : M63AmbientGeometry F) :
    ∀ circumference (h : 0 < circumference), ∀ t ∈ Set.Icc a b,
      M64AnnulusProjection (G.product circumference h) t := by
  intro circumference h t ht c0 c1 A
  exact m64ProjectedAnnulus_of_annulus (G.product circumference h) t c0 c1 A




def m64FlowConclusion_of_fields
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}
    (G : M63AmbientGeometry F)
    (evolution : M64AnnulusEvolution G)
    (ramp_comparison : M64RampSmallAnnulusComparison G)
    (projection : ∀ circumference (h : 0 < circumference), ∀ t ∈ Set.Icc a b,
      M64AnnulusProjection (G.product circumference h) t) :
    M64FlowConclusion F := by
  exact { geometry := G
          evolution := evolution
          ramp_comparison := ramp_comparison
          projection := projection }




theorem m64ThreeDimensionalFlowConclusion_of_fields
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
    (flow : M64FlowConclusion F)
    (approximation : M64FamilyApproximationTheory F flow.geometry)
    (disks : ∀ circumference (h : 0 < circumference), ∀ t ∈ Set.Icc a b,
      M64DiskAreaComparison (flow.geometry.product circumference h) t)
    (finite_nets : M64FamilyAnnulusNets flow.geometry) :
    Nonempty (M64ThreeDimensionalFlowConclusion F) := by
  exact ⟨{ flow := flow
           approximation := approximation
           disks := disks
           finite_nets := finite_nets }⟩

end PoincareConjecture
