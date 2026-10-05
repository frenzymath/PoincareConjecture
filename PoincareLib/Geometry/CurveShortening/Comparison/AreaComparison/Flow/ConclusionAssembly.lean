import PoincareLib.Geometry.CurveShortening.Comparison.Theory
import PoincareLib.Geometry.CurveShortening.Comparison.AreaComparison.Projection.Complete

/-!
Assembling the proved evolution, small-annulus, projection, approximation, disk and finite-net
fields into the frozen flow conclusions.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- Turn the actual projected-annulus constructor into the universal projection field.
Source: Assembly of MT Lemmas 19.15, 19.30 and 19.31, pp. 447-449 and 462, in the frozen M64
contract. -/
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

/-- Package one ambient geometry with its actual evolution, ramp comparison, and projection
services. Source: Assembly of MT Lemmas 19.15, 19.30 and 19.31, pp. 447-449 and 462, in the
frozen M64 contract. -/
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

/-- Retain the same flow geometry while adding the actual disk comparison and finite-net
services. Source: Assembly of MT Lemmas 19.15, 19.30 and 19.31, pp. 447-449 and 462, in the
frozen M64 contract. -/
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

end PoincareMT
