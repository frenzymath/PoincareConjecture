import PoincareLib.Geometry.Riemannian.LoopSpace.Area.PlaneReflection
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Derivative.Manifold.Equiv
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.AreaEnergy

/-!
# Area invariance under reflection of the disk

Morgan-Tian Definition 18.17, printed p. 430, boundary regularization.
Reflection changes the sign of one differential column and preserves
the Gram determinant. It preserves volume and the integration disk,
so actual integrability and area are unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Reflection preserves the actual totalized area density. Source:
MT Definition 18.17, p. 430, reflected-area derivation. -/
theorem m60AreaDensity_comp_reflection (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) :
    m60AreaDensity g (fun w => f (m60PlaneReflection w)) z =
      m60AreaDensity g f (m60PlaneReflection z) := by
  have hd := M60.mfderiv_comp_continuousLinearEquiv
    (I := 𝓡 n) f m60PlaneReflection.toContinuousLinearEquiv z
  have h0 : mfderiv (𝓡 2) (𝓡 n) (fun w => f (m60PlaneReflection w)) z
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      mfderiv (𝓡 2) (𝓡 n) f (m60PlaneReflection z) (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
    erw [hd]
    change mfderiv (𝓡 2) (𝓡 n) f (m60PlaneReflection z)
      (m60PlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 0)) = _
    rw [m60PlaneReflection_basis_zero]
  have h1 : mfderiv (𝓡 2) (𝓡 n) (fun w => f (m60PlaneReflection w)) z
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      -mfderiv (𝓡 2) (𝓡 n) f (m60PlaneReflection z) (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
    erw [hd]
    change mfderiv (𝓡 2) (𝓡 n) f (m60PlaneReflection z)
      (m60PlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = _
    rw [m60PlaneReflection_basis_one, map_neg]
  simp only [m60AreaDensity, Matrix.det_fin_two, m60AreaGram, h0, h1, map_neg,
    neg_apply, neg_neg, neg_mul_neg]

/-- Reflection preserves area integrability on the disk. Source:
MT Definition 18.17, p. 430, reflected-disk admissibility. -/
theorem m60AreaDensity_integrableOn_comp_reflection (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : IntegrableOn (m60AreaDensity g f) loopDiskSet volume) :
    IntegrableOn (m60AreaDensity g (fun w => f (m60PlaneReflection w))) loopDiskSet volume := by
  have hi := (m60PlaneReflection.measurePreserving.integrableOn_comp_preimage
    m60PlaneReflection.toMeasurableEquiv.measurableEmbedding).mpr hf
  rw [m60PlaneReflection_preimage_disk] at hi
  change IntegrableOn (fun z => m60AreaDensity g (fun w => f (m60PlaneReflection w)) z)
    loopDiskSet volume
  simp_rw [m60AreaDensity_comp_reflection]
  exact hi

/-- Reflection preserves the actual disk area integral. Source:
MT Definition 18.17, p. 430, reflected-area derivation. -/
theorem m60AreaIntegral_comp_reflection (g : RiemannianMetric n M) (f : LoopPlane → M) :
    (∫ z in loopDiskSet, m60AreaDensity g (fun w => f (m60PlaneReflection w)) z) =
      ∫ z in loopDiskSet, m60AreaDensity g f z := by
  simp_rw [m60AreaDensity_comp_reflection]
  have h := m60PlaneReflection.measurePreserving.setIntegral_preimage_emb
    m60PlaneReflection.toMeasurableEquiv.measurableEmbedding (m60AreaDensity g f) loopDiskSet
  rwa [m60PlaneReflection_preimage_disk] at h

end PoincareMT
