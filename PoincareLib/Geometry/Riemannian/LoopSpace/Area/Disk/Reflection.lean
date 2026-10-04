import PoincareLib.Geometry.Riemannian.LoopSpace.Area.ReflectedArea
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Reparameterization
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Disk.Regularity

/-!
# Reflection preserves admissible filling disks

Morgan-Tian Definition 18.17, printed p. 430, boundary regularization.
The reflected disk has the same actual metric Lipschitz constant and
area. Its boundary homeomorphism is composed with circle reflection.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

omit [T2Space M] in
/-- The reflected disk retains its actual metric Lipschitz constant.
Source: MT Definition 18.17, p. 430, reflected-disk admissibility. -/
theorem m60Disk_reflection_lipschitz (g : RiemannianMetric 3 M)
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g gamma) (x y : LoopDisk) :
    g.edist (D.map (m60PlaneReflection x)) (D.map (m60PlaneReflection y)) ≤
      ENNReal.ofReal D.lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
  have hmem (z : LoopDisk) : m60PlaneReflection z.val ∈ loopDiskSet := by
    change z.val ∈ m60PlaneReflection ⁻¹' loopDiskSet
    rw [m60PlaneReflection_preimage_disk]
    exact z.property
  have h := D.lipschitz_on_disk ⟨m60PlaneReflection x, hmem x⟩
    ⟨m60PlaneReflection y, hmem y⟩
  simpa only [← map_sub, m60PlaneReflection.norm_map] using h

/-- Reflection of an admissible filling disk, with the correctly
composed boundary homeomorphism. Source: MT Definition 18.17,
p. 430, reflected-disk derivation. -/
noncomputable def m60Disk_reflect (g : RiemannianMetric 3 M)
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g gamma) :
    LipschitzSpanningDisk g gamma where
  map := fun z => D.map (m60PlaneReflection z)
  continuous_on_disk := D.continuous_on_disk.comp m60PlaneReflection.continuous.continuousOn
    (fun z hz => by
      change z ∈ m60PlaneReflection ⁻¹' loopDiskSet
      rwa [m60PlaneReflection_preimage_disk])
  ae_manifold_differentiable := m60_ae_mdifferentiable_of_disk_lipschitz g
    D.lipschitz_nonnegative (m60Disk_reflection_lipschitz g D)
  reparameterization := m60CircleReflection.trans D.reparameterization
  boundary_eq := fun z => D.boundary_eq (m60CircleReflection.map z)
  lipschitz_constant := D.lipschitz_constant
  lipschitz_nonnegative := D.lipschitz_nonnegative
  lipschitz_on_disk := m60Disk_reflection_lipschitz g D
  area_integrable := m60AreaDensity_integrableOn_comp_reflection g D.map D.area_integrable
  area_nonnegative := by
    change 0 ≤ ∫ z in loopDiskSet, m60AreaDensity g (fun w => D.map (m60PlaneReflection w)) z
    rw [m60AreaIntegral_comp_reflection]
    exact D.area_nonnegative

/-- Reflection preserves the area of every admissible disk. Source:
MT Definition 18.17, p. 430, reflected-disk derivation. -/
theorem m60Disk_reflect_area (g : RiemannianMetric 3 M)
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g gamma) :
    (m60Disk_reflect g D).area = D.area := m60AreaIntegral_comp_reflection g D.map

end PoincareMT
