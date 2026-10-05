import PoincareLib.Geometry.CurveShortening.Comparison.Approximation
import PoincareLib.Geometry.CurveShortening.Ramp.Estimates

/-!
# M64 uniform polygon approximation and the exact evolving family

Morgan--Tian Definition 19.18, Claims 19.19-19.20, Corollary 19.21,
Lemma 19.17 and Claim 19.22, pp. 449-453. Thresholds precede both polygon
count and family member. The evolving family retains the literal static
approximation and applied estimates on those same solutions for M65.

Source and primitive contract: reviews/contracts/M64-round1.md.
Corrections: reviews/errata/2026-09-14-m64-annulus-comparison.md and the
2015 correction's dependence on initial length and total curvature.
These statements contain no predecessor theorem service or admission.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- Static approximation for the actual metric and compatible connection.
The full M64 theorem supplies this for compact Hausdorff second-countable
smooth three-manifolds. Nullity is required only for the disk conclusions. -/
structure M64StaticApproximationTheory (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) : Prop where
  sampled_exists : ∀ gamma : C1FreeLoopSpace (M := M), ∀ N : ℕ, 0 < N →
    ∃ polygon : M63GeodesicPolygon g D N,
      M64SampledPolygon gamma polygon ∧ Nonempty (M64PolygonBoundary polygon)
  polygon_length : ∀ N : ℕ, 0 < N → ∀ polygon : M63GeodesicPolygon g D N,
    m64PolygonLength polygon = ∑ j : Fin N, m63CellLength N * (polygon.side j).speed
  uniform_compact : ∀ X : Set (C1FreeLoopSpace (M := M)), IsCompact X →
    ∀ zeta : ℝ, 0 < zeta → ∃ N0 : ℕ, 0 < N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ gamma : C1FreeLoopSpace (M := M), gamma ∈ X →
        ∃ polygon : M63GeodesicPolygon g D N,
          M64SampledPolygon gamma polygon ∧
          (∀ other : M63GeodesicPolygon g D N, M64SampledPolygon gamma other →
            ∀ x, other.map x = polygon.map x) ∧
          Nonempty (M64PolygonBoundary polygon) ∧
          (0 ≤ freeLoopLength g gamma - m64PolygonLength polygon ∧
            freeLoopLength g gamma - m64PolygonLength polygon < zeta) ∧
          ∃ A : M64Annulus g (periodicFreeLoop gamma) polygon.map,
            M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
              0 ≤ A.area ∧ A.area < zeta
  raw_family : ∀ Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily Gamma → ∀ zeta : ℝ, 0 < zeta →
      ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
        ∃ A : M64RawFamilyApproximation g D Gamma zeta, A.count = N

variable {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}

/-- Applied geometric estimates for every displayed solution. The chosen
products, curves, time slab and three constants are exactly those of C. -/
structure M64AppliedFamilyEstimates (G : M63AmbientGeometry F)
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    {zeta : ℝ} (C : M63FamilyConclusion G Gamma zeta) : Prop where
  curve_estimates : ∀ circumference (h : 0 < circumference), ∀ z : LoopTwoSphere,
    M63C2CurveEstimates (G.product circumference h).flow
      ((C.solutions circumference h).curve z) b G.K0 G.K1 G.K2

/-- The all-N approximation with its exact M63 family and applied estimates.
Equality of the retained approximation identifies the same polygon maps,
flattened C1 loops, initial ramps and all subsequent projected families. -/
structure M64EvolvingApproximation (G : M63AmbientGeometry F)
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (zeta : ℝ) (N : ℕ) where
  raw : M64RawFamilyApproximation (F.metric a) (F.connection a) Gamma zeta
  count_eq : raw.count = N
  family : M63FamilyConclusion G Gamma zeta
  approximation_eq : family.approximation = raw.toM63
  estimates : M64AppliedFamilyEstimates G family

/-- Full all-N construction on the one selected actual product geometry.
The universal M63 analytic service is used by the M64 proof, then only its
applied conclusions on the returned solutions are retained. -/
def M64FamilyApproximationTheory (F : RicciFlow 3 M (Set.Icc a b))
    (G : M63AmbientGeometry F) : Prop :=
  ∀ Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily Gamma → ∀ zeta : ℝ, 0 < zeta →
      ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
        Nonempty (M64EvolvingApproximation G Gamma zeta N)

end PoincareMT
