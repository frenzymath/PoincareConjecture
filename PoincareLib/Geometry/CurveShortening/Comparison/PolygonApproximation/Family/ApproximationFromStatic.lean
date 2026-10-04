import PoincareLib.Geometry.CurveShortening.Comparison.FamilyAdapters
import PoincareLib.Geometry.CurveShortening.Comparison.ApproximationTheory

/-!
# Applying the static raw-family supplier

The static record supplies an M64 raw approximation at every sufficiently
large count.  This file applies the checked M63 family adapter separately at
each count, retaining the same raw record and the selected analytic geometry.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {G : M63AmbientGeometry F}

/-- Turn an M64 raw-family supplier into the all-count evolving-family conclusion, using the
already selected M63 analytic geometry. Source: Auxiliary step for MT Definition 19.18 and
Claims 19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64FamilyApproximationTheory_from_static_raw
    (hM63 : M63RampEstimatesTheory.{u})
    (compact : IsCompact (Set.univ : Set M))
    (analytic : M63AnalyticConclusion F G)
    (raw_family : ∀ Gamma : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := M)), M61NullFamily Gamma →
      ∀ zeta : ℝ, 0 < zeta → ∃ N0 : ℕ, 0 < N0 ∧
        ∀ N : ℕ, N0 ≤ N →
          ∃ A : M64RawFamilyApproximation (F.metric a) (F.connection a) Gamma zeta,
            A.count = N) :
    M64FamilyApproximationTheory F G := by
  intro Gamma hnull zeta hzeta
  obtain ⟨N0, hN0, hraw⟩ := raw_family Gamma hnull zeta hzeta
  refine ⟨N0, hN0, ?_⟩
  intro N hNN
  obtain ⟨raw, hcount⟩ := hraw N hNN
  exact m64EvolvingApproximation_from_M63 hM63 compact analytic hnull hzeta raw hcount

end PoincareMT
