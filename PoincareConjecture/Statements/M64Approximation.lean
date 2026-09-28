import PoincareConjecture.Definitions.M64Approximation
import PoincareConjecture.Statements.M63RampEstimates















set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




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



structure M64AppliedFamilyEstimates (G : M63AmbientGeometry F)
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    {zeta : ℝ} (C : M63FamilyConclusion G Gamma zeta) : Prop where
  curve_estimates : ∀ circumference (h : 0 < circumference), ∀ z : LoopTwoSphere,
    M63C2CurveEstimates (G.product circumference h).flow
      ((C.solutions circumference h).curve z) b G.K0 G.K1 G.K2




structure M64EvolvingApproximation (G : M63AmbientGeometry F)
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (zeta : ℝ) (N : ℕ) where
  raw : M64RawFamilyApproximation (F.metric a) (F.connection a) Gamma zeta
  count_eq : raw.count = N
  family : M63FamilyConclusion G Gamma zeta
  approximation_eq : family.approximation = raw.toM63
  estimates : M64AppliedFamilyEstimates G family




def M64FamilyApproximationTheory (F : RicciFlow 3 M (Set.Icc a b))
    (G : M63AmbientGeometry F) : Prop :=
  ∀ Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily Gamma → ∀ zeta : ℝ, 0 < zeta →
      ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
        Nonempty (M64EvolvingApproximation G Gamma zeta N)

end PoincareConjecture
