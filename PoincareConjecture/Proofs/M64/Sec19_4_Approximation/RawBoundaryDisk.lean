import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.Reparameterization















set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}





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




theorem m64RawDiskOfBoundaryReparam_area
    {gamma : C1FreeLoopSpace (M := M)}
    {boundary : ContinuousMap LoopCircle M}
    (r : CircleReparameterization)
    (h : ∀ z : LoopCircle, boundary z = gamma (r.map z))
    (D : LipschitzSpanningDisk g gamma) :
    (m64RawDiskOfBoundaryReparam r h D).area = D.area := rfl




theorem m64C1DiskOfBoundaryReparam_area
    {gamma : C1FreeLoopSpace (M := M)}
    {boundary : ContinuousMap LoopCircle M}
    (r : CircleReparameterization)
    (h : ∀ z : LoopCircle, boundary z = gamma (r.map z))
    (D : M64RawSpanningDisk g boundary) :
    (m64C1DiskOfBoundaryReparam r h D).area = D.area := rfl





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




theorem m64RawFillingArea_eq_fillingArea_of_boundary_reparam
    {gamma : C1FreeLoopSpace (M := M)}
    {boundary : ContinuousMap LoopCircle M}
    (r : CircleReparameterization)
    (h : ∀ z : LoopCircle, boundary z = gamma (r.map z)) :
    m64RawFillingArea g boundary = fillingArea g gamma := by
  unfold m64RawFillingArea fillingArea
  rw [m64RawDiskAreaRange_eq_of_boundary_reparam r h]

end PoincareConjecture
