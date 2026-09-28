import PoincareConjecture.Definitions.M64Annulus

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {gamma : C1FreeLoopSpace (M := M)}

def m64RawDiskOfC1 (D : LipschitzSpanningDisk g gamma) :
    M64RawSpanningDisk g (m64C1Boundary gamma) where
  map := D.map
  continuous_on_disk := D.continuous_on_disk
  ae_manifold_differentiable := D.ae_manifold_differentiable
  reparameterization := D.reparameterization
  boundary_eq := D.boundary_eq
  lipschitz_constant := D.lipschitz_constant
  lipschitz_nonnegative := D.lipschitz_nonnegative
  lipschitz_on_disk := D.lipschitz_on_disk
  area_integrable := D.area_integrable
  area_nonnegative := D.area_nonnegative

def m64C1DiskOfRaw (D : M64RawSpanningDisk g (m64C1Boundary gamma)) :
    LipschitzSpanningDisk g gamma where
  map := D.map
  continuous_on_disk := D.continuous_on_disk
  ae_manifold_differentiable := D.ae_manifold_differentiable
  reparameterization := D.reparameterization
  boundary_eq := D.boundary_eq
  lipschitz_constant := D.lipschitz_constant
  lipschitz_nonnegative := D.lipschitz_nonnegative
  lipschitz_on_disk := D.lipschitz_on_disk
  area_integrable := D.area_integrable
  area_nonnegative := D.area_nonnegative

def m64C1RawDiskEquiv :
    LipschitzSpanningDisk g gamma ≃ M64RawSpanningDisk g (m64C1Boundary gamma) where
  toFun := m64RawDiskOfC1
  invFun := m64C1DiskOfRaw
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem m64RawDiskOfC1_area (D : LipschitzSpanningDisk g gamma) :
    (m64RawDiskOfC1 D).area = D.area := rfl

theorem m64C1DiskOfRaw_area (D : M64RawSpanningDisk g (m64C1Boundary gamma)) :
    (m64C1DiskOfRaw D).area = D.area := rfl

theorem m64RawDiskAreaRange_c1 :
    m64RawDiskAreaRange g (m64C1Boundary gamma) =
      Set.range (fun D : LipschitzSpanningDisk g gamma => D.area) := by
  ext area
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨m64C1DiskOfRaw D, hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨m64RawDiskOfC1 D, hD⟩

theorem m64RawFillingArea_c1 :
    m64RawFillingArea g (m64C1Boundary gamma) = fillingArea g gamma := by
  unfold m64RawFillingArea fillingArea
  rw [m64RawDiskAreaRange_c1]

end PoincareConjecture
