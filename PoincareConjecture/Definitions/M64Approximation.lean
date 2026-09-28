import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Definitions.M63Family














set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture


noncomputable def m64LoopCircleParam (x : ℝ) : LoopCircle :=
  ⟨!₂[Real.cos x, Real.sin x], by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.cos_sq_add_sin_sq]⟩

section Polygons

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {N : ℕ}



structure M64PolygonBoundary (polygon : M63GeodesicPolygon g D N) where
  map : ContinuousMap LoopCircle M
  angular_eq : ∀ x, map (m64LoopCircleParam x) = polygon.map x



noncomputable def m64PolygonLength (polygon : M63GeodesicPolygon g D N) : ℝ :=
  ∫ x in (0 : ℝ)..curvePeriod,
    g.tangentNorm (polygon.map x) (curveVelocity (n := n) polygon.map x)

end Polygons

section Families

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {N : ℕ}



def M64SampledPolygon (gamma : C1FreeLoopSpace (M := M))
    (polygon : M63GeodesicPolygon g D N) : Prop :=
  ∀ j : Fin N, polygon.vertices j = periodicFreeLoop gamma (m63CellLeft N j)




structure M64RawFamilyApproximation (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g)
    (Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)))
    (zeta : ℝ) where
  count : ℕ
  count_positive : 0 < count
  polygon : LoopTwoSphere → M63GeodesicPolygon g D count
  sampled : ∀ z, M64SampledPolygon (Gamma z) (polygon z)
  boundary : ∀ z, M64PolygonBoundary (polygon z)
  polygon_continuous : Continuous (fun p : LoopTwoSphere × ℝ => (polygon p.1).map p.2)
  boundary_continuous : Continuous (fun p : LoopTwoSphere × LoopCircle => (boundary p.1).map p.2)
  polygon_length : ∀ z, m64PolygonLength (polygon z) =
    ∑ j : Fin count, m63CellLength count * ((polygon z).side j).speed
  raw_null : ∀ z, M64RawNullLoop (boundary z).map
  source_filling : ∀ z, FillingAreaData g (Gamma z)
  raw_disk_nonempty : ∀ z, Nonempty (M64RawSpanningDisk g (boundary z).map)
  raw_area_bounded_below : ∀ z, BddBelow (m64RawDiskAreaRange g (boundary z).map)
  raw_area_nonnegative : ∀ z, 0 ≤ m64RawFillingArea g (boundary z).map
  raw_area_error : ∀ z,
    |m64RawFillingArea g (boundary z).map - fillingArea g (Gamma z)| < zeta
  annulus : ∀ z, M64Annulus g (periodicFreeLoop (Gamma z)) (polygon z).map
  annulus_piecewise : ∀ z, M64PiecewiseC1Annulus (annulus z)
  annulus_geodesic : ∀ z, M64GeodesicAnnulus D (annulus z)
  annulus_area : ∀ z, 0 ≤ (annulus z).area ∧ (annulus z).area < zeta
  family : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))
  null_family : M61NullFamily family
  homotopic : Gamma.Homotopic family
  angular_eq : ∀ z x,
    periodicFreeLoop (family z) x = m63FlattenedPolygon (polygon z) x
  angular_smooth : ∀ z,
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞ (periodicFreeLoop (family z))
  first_jet_continuous : Continuous (fun p : LoopTwoSphere × ℝ =>
    m63AngularFirstJet (n := 3) (periodicFreeLoop (family p.1)) p.2)
  second_jet_continuous : Continuous (fun p : LoopTwoSphere × ℝ =>
    m63AngularSecondJet D (periodicFreeLoop (family p.1)) p.2)
  flattened_length : ∀ z, freeLoopLength g (family z) = m64PolygonLength (polygon z)
  family_filling : ∀ z, FillingAreaData g (family z)
  flattening_area_range : ∀ z,
    m64RawDiskAreaRange g (boundary z).map =
      Set.range (fun disk : LipschitzSpanningDisk g (family z) => disk.area)
  length_loss : ∀ z,
    0 ≤ freeLoopLength g (Gamma z) - freeLoopLength g (family z) ∧
      freeLoopLength g (Gamma z) - freeLoopLength g (family z) < zeta
  area_error : ∀ z, |fillingArea g (family z) - fillingArea g (Gamma z)| < zeta



def M64RawFamilyApproximation.toM63 {a b : ℝ}
    {F : RicciFlow 3 M (Set.Icc a b)}
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    {zeta : ℝ}
    (A : M64RawFamilyApproximation (F.metric a) (F.connection a) Gamma zeta) :
    M63RawApproximation F Gamma zeta where
  count := A.count
  count_positive := A.count_positive
  polygon := A.polygon
  sample_eq := A.sampled
  family := A.family
  null_family := A.null_family
  homotopic := A.homotopic
  angular_eq := A.angular_eq
  angular_smooth := A.angular_smooth
  first_jet_continuous := A.first_jet_continuous
  second_jet_continuous := A.second_jet_continuous
  length_loss := A.length_loss
  area_error := A.area_error

end Families

end PoincareConjecture
