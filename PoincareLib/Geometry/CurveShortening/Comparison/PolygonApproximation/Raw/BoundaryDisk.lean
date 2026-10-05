import PoincareLib.Geometry.CurveShortening.Comparison.Annulus
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Reparameterization

/-!
# Transporting disks to a polygon boundary

The raw M64 disk class differs from the C1 class only by the displayed
boundary map.  Once that map is known to be a circle reparameterization of a
C1 loop, the two disk classes are transported without changing the disk map,
Jacobian, or area.  This is the missing bridge needed by raw-family assembly;
constructing the reparameterization itself remains a separate polygon/profile
interface.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- Transport a C1 spanning disk to an arbitrary continuous boundary that is the target loop
after a circle reparameterization. Source: Auxiliary step for MT Definition 19.18 and Claims
19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
def m64RawDiskOfBoundaryReparam
    {gamma : C1FreeLoopSpace (M := M)}
    {boundary : ContinuousMap LoopCircle M}
    (r : CircleReparameterization)
    (h : ∀ z : LoopCircle, boundary z = gamma (r.map z))
    (D : LipschitzSpanningDisk g gamma) :
    M64RawSpanningDisk g boundary where
  map := D.map
  continuous_on_disk := D.continuous_on_disk
  ae_manifold_differentiable := D.ae_manifold_differentiable
  reparameterization := D.reparameterization.trans r.symm
  boundary_eq := by
    intro z
    rw [D.boundary_eq, h]
    change gamma (D.reparameterization.map z) =
      gamma (r.map (r.inverse (D.reparameterization.map z)))
    rw [r.right_inverse]
  lipschitz_constant := D.lipschitz_constant
  lipschitz_nonnegative := D.lipschitz_nonnegative
  lipschitz_on_disk := D.lipschitz_on_disk
  area_integrable := D.area_integrable
  area_nonnegative := D.area_nonnegative

/-- Transport a raw disk back to the C1 loop whose reparameterization gives the displayed
raw boundary. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp.
450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
def m64C1DiskOfBoundaryReparam
    {gamma : C1FreeLoopSpace (M := M)}
    {boundary : ContinuousMap LoopCircle M}
    (r : CircleReparameterization)
    (h : ∀ z : LoopCircle, boundary z = gamma (r.map z))
    (D : M64RawSpanningDisk g boundary) :
    LipschitzSpanningDisk g gamma where
  map := D.map
  continuous_on_disk := D.continuous_on_disk
  ae_manifold_differentiable := D.ae_manifold_differentiable
  reparameterization := D.reparameterization.trans r
  boundary_eq := by
    intro z
    rw [D.boundary_eq, h]
    rfl
  lipschitz_constant := D.lipschitz_constant
  lipschitz_nonnegative := D.lipschitz_nonnegative
  lipschitz_on_disk := D.lipschitz_on_disk
  area_integrable := D.area_integrable
  area_nonnegative := D.area_nonnegative

/-- Reinterpreting the boundary parameterization preserves the literal disk map and area.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64RawDiskOfBoundaryReparam_area
    {gamma : C1FreeLoopSpace (M := M)}
    {boundary : ContinuousMap LoopCircle M}
    (r : CircleReparameterization)
    (h : ∀ z : LoopCircle, boundary z = gamma (r.map z))
    (D : LipschitzSpanningDisk g gamma) :
    (m64RawDiskOfBoundaryReparam r h D).area = D.area := rfl

/-- Restoring the C1 boundary interpretation preserves the literal disk map and area.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64C1DiskOfBoundaryReparam_area
    {gamma : C1FreeLoopSpace (M := M)}
    {boundary : ContinuousMap LoopCircle M}
    (r : CircleReparameterization)
    (h : ∀ z : LoopCircle, boundary z = gamma (r.map z))
    (D : M64RawSpanningDisk g boundary) :
    (m64C1DiskOfBoundaryReparam r h D).area = D.area := rfl

/-- The raw polygon-boundary area range equals the ordinary C1 filling area range whenever
the boundary is a circle reparameterization of the loop. Source: Morgan--Tian Definition
19.18 and Claims 19.19-19.22, printed pp. 450-453; exact construction reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-full-round1-source-review.md`. -/
theorem m64RawDiskAreaRange_eq_of_boundary_reparam
    {gamma : C1FreeLoopSpace (M := M)}
    {boundary : ContinuousMap LoopCircle M}
    (r : CircleReparameterization)
    (h : ∀ z : LoopCircle, boundary z = gamma (r.map z)) :
    m64RawDiskAreaRange g boundary =
      Set.range (fun D : LipschitzSpanningDisk g gamma => D.area) := by
  ext area
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨m64C1DiskOfBoundaryReparam r h D, hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨m64RawDiskOfBoundaryReparam r h D, hD⟩

/-- Boundary relabeling preserves the full disk area range and hence its totalized infimum.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64RawFillingArea_eq_fillingArea_of_boundary_reparam
    {gamma : C1FreeLoopSpace (M := M)}
    {boundary : ContinuousMap LoopCircle M}
    (r : CircleReparameterization)
    (h : ∀ z : LoopCircle, boundary z = gamma (r.map z)) :
    m64RawFillingArea g boundary = fillingArea g gamma := by
  unfold m64RawFillingArea fillingArea
  rw [m64RawDiskAreaRange_eq_of_boundary_reparam r h]

end PoincareMT
