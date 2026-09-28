import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.ReflectedArea
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.Reparameterization
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskRegularity









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

omit [T2Space M] in


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



theorem m60Disk_reflect_area (g : RiemannianMetric 3 M)
    {gamma : C1FreeLoopSpace (M := M)} (D : LipschitzSpanningDisk g gamma) :
    (m60Disk_reflect g D).area = D.area := m60AreaIntegral_comp_reflection g D.map

end PoincareConjecture
