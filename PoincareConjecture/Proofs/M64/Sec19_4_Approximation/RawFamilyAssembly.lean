import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.PolygonLength
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.RawBoundaryDisk
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.RawDiskGuards
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskExistence
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.FlattenedPolygonLength
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.SampledPolygonLength

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
  {zeta : ℝ}

structure M64RawBoundaryAnnulusPackage
    (A : M63RawApproximation F Gamma zeta) where
  boundary : ∀ z, M64PolygonBoundary (A.polygon z)
  reparam : LoopTwoSphere → CircleReparameterization
  boundary_eq_family : ∀ z w,
    (boundary z).map w = (A.family z) ((reparam z).map w)
  polygon_continuous :
    Continuous (fun p : LoopTwoSphere × ℝ => (A.polygon p.1).map p.2)
  boundary_continuous :
    Continuous (fun p : LoopTwoSphere × LoopCircle => (boundary p.1).map p.2)
  raw_null : ∀ z, M64RawNullLoop (boundary z).map
  annulus : ∀ z,
    M64Annulus (F.metric a) (periodicFreeLoop (Gamma z)) (A.polygon z).map
  annulus_piecewise : ∀ z, M64PiecewiseC1Annulus (annulus z)
  annulus_geodesic : ∀ z, M64GeodesicAnnulus (F.connection a) (annulus z)
  annulus_area : ∀ z, 0 ≤ (annulus z).area ∧ (annulus z).area < zeta

noncomputable def m64RawFamilyApproximation_of_M63
    (hnull : M61NullFamily Gamma)
    (A : M63RawApproximation F Gamma zeta)
    (P : M64RawBoundaryAnnulusPackage A) :
    M64RawFamilyApproximation (F.metric a) (F.connection a) Gamma zeta := by
  let g := F.metric a
  let D := F.connection a
  have hsource (z : LoopTwoSphere) : FillingAreaData g (A.family z) :=
    Classical.choice (m60FillingData_of_null g (A.family z) (A.null_family z))
  let rawDisk : ∀ z : LoopTwoSphere,
      M64RawSpanningDisk g (P.boundary z).map := fun z =>
    m64RawDiskOfBoundaryReparam (P.reparam z) (P.boundary_eq_family z)
      (Classical.choice (hsource z).nonempty)
  have hlengthEq (z : LoopTwoSphere) :
      freeLoopLength g (A.family z) =
        ∑ j : Fin A.count,
          m63CellLength A.count * ((A.polygon z).side j).speed := by
    have hrep : periodicFreeLoop (A.family z) =
        m63FlattenedPolygon (A.polygon z) := funext (A.angular_eq z)
    have hflat : freeLoopLength g (A.family z) =
        m62Length F (fun x _ => m63FlattenedPolygon (A.polygon z) x) a := by
      unfold freeLoopLength
      rw [hrep]
      rfl
    rw [hflat, m63FlattenedPolygon_length F a (A.polygon z) A.count_positive]
  refine {
    count := A.count
    count_positive := A.count_positive
    polygon := A.polygon
    sampled := A.sample_eq
    boundary := P.boundary
    polygon_continuous := P.polygon_continuous
    boundary_continuous := P.boundary_continuous
    polygon_length := fun z => m64PolygonLength_eq_sum
      (A.polygon z) A.count_positive
    raw_null := P.raw_null
    source_filling := fun z =>
      Classical.choice (m60FillingData_of_null g (Gamma z) (hnull z))
    raw_disk_nonempty := fun z => ⟨rawDisk z⟩
    raw_area_bounded_below := fun z => m64RawDiskAreaRange_bddBelow (rawDisk z)
    raw_area_nonnegative := fun z => m64RawFillingArea_nonnegative (rawDisk z)
    raw_area_error := ?_
    annulus := P.annulus
    annulus_piecewise := P.annulus_piecewise
    annulus_geodesic := P.annulus_geodesic
    annulus_area := P.annulus_area
    family := A.family
    null_family := A.null_family
    homotopic := A.homotopic
    angular_eq := A.angular_eq
    angular_smooth := A.angular_smooth
    first_jet_continuous := A.first_jet_continuous
    second_jet_continuous := A.second_jet_continuous
    flattened_length := fun z => by
      calc
        freeLoopLength g (A.family z) =
            ∑ j : Fin A.count,
              m63CellLength A.count * ((A.polygon z).side j).speed := hlengthEq z
        _ = m64PolygonLength (A.polygon z) :=
          (m64PolygonLength_eq_sum (A.polygon z) A.count_positive).symm
    family_filling := hsource
    flattening_area_range := ?_
    length_loss := A.length_loss
    area_error := A.area_error }
  · intro z
    rw [m64RawFillingArea_eq_fillingArea_of_boundary_reparam
      (P.reparam z) (P.boundary_eq_family z)]
    exact A.area_error z
  · intro z
    exact m64RawDiskAreaRange_eq_of_boundary_reparam
      (P.reparam z) (P.boundary_eq_family z)

end PoincareConjecture
