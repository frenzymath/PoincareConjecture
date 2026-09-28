import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.PlaneReflection
import PoincareConjecture.Proofs.M60.Mathlib.ManifoldDerivativeEquiv
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

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

theorem m60AreaIntegral_comp_reflection (g : RiemannianMetric n M) (f : LoopPlane → M) :
    (∫ z in loopDiskSet, m60AreaDensity g (fun w => f (m60PlaneReflection w)) z) =
      ∫ z in loopDiskSet, m60AreaDensity g f z := by
  simp_rw [m60AreaDensity_comp_reflection]
  have h := m60PlaneReflection.measurePreserving.setIntegral_preimage_emb
    m60PlaneReflection.toMeasurableEquiv.measurableEmbedding (m60AreaDensity g f) loopDiskSet
  rwa [m60PlaneReflection_preimage_disk] at h

end PoincareConjecture
