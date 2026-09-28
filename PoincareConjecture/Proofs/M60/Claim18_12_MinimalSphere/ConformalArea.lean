import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.ConformalFactor
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.ConformalRicciTrace
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundVolume
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.LocalFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60SphereAreaDensity_eq_conformalFactor_mul (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (hc : M60WeaklyConformal g f) (z : LoopPlane) :
    m60SphereAreaDensity g f z = m60SphereConformalFactor g f (m60SphereParameter z) *
      (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  have h := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G 0 0)
    (m60AreaGram_eq_diagonal_of_weaklyConformal g f hf hc z)
  simp only [Matrix.diagonal_apply_eq] at h
  rw [← h]
  unfold m60AreaGram
  rw [mfderiv_comp z (hf.mdifferentiable (by simp) _)
    (m60SphereParameter_contMDiff.mdifferentiable (by simp) _)]
  change g.inner _ (mfderiv (𝓡 2) (𝓡 n) f _
    (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z (EuclideanSpace.basisFun (Fin 2) ℝ 0)))
    (mfderiv (𝓡 2) (𝓡 n) f _
      (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z (EuclideanSpace.basisFun (Fin 2) ℝ 0))) = _
  rw [m60SphereConformalFactor_spec g f hc, m60SphereParameter_inner]
  simp

theorem m60SphereArea_eq_integral_conformalFactor (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hc : M60WeaklyConformal g f) :
    m60SphereArea g f = ∫ p, m60SphereConformalFactor g f p
      ∂m60RoundSphereMetric.volumeMeasure := by
  rw [m60RoundSphereMetric_integral _ (m60SphereConformalFactor_contMDiff g f hf hc).continuous]
  unfold m60SphereArea
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (m60SphereAreaDensity_eq_conformalFactor_mul g f (hf.of_le (by simp)) hc)

theorem m60SphereConformalFactor_integrable (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hc : M60WeaklyConformal g f) :
    Integrable (m60SphereConformalFactor g f) m60RoundSphereMetric.volumeMeasure :=
  (m60SphereConformalFactor_contMDiff g f hf hc).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem m60SphereConformalFactor_ae_pos (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hc : M60WeaklyConformal g f)
    (hb : (m60SphereBranchSet (n := n) f).Finite) :
    ∀ᵐ p ∂m60RoundSphereMetric.volumeMeasure, 0 < m60SphereConformalFactor g f p := by
  let : NullSingletonClass m60RoundSphereMetric.volumeMeasure :=
    ⟨m60RoundSphereMetric_volume_singleton⟩
  have hnull := hb.measure_zero (μ := m60RoundSphereMetric.volumeMeasure)
  have hae : ∀ᵐ p ∂m60RoundSphereMetric.volumeMeasure,
      p ∉ m60SphereBranchSet (n := n) f := by
    rw [ae_iff]
    simp only [not_not]
    exact hnull
  filter_upwards [hae] with p hp
  exact lt_of_le_of_ne (m60SphereConformalFactor_nonneg g f p)
    (Ne.symm fun h => hp ((m60SphereConformalFactor_eq_zero_iff g f hc p).mp h))

end PoincareConjecture
