import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundVolume
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Coordinates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture



theorem m60SphereParameter_mfderiv_isInvertible (z : LoopPlane) :
    (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z).IsInvertible := by
  have he : m60SphereChart.symm.MDifferentiable (𝓡 2) (𝓡 2) := by
    constructor
    · rw [m60SphereChart_eq_chartAt]
      exact (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞)).mdifferentiableOn (by simp)
    · rw [m60SphereChart_eq_chartAt]
      exact (contMDiffOn_chart (I := 𝓡 2) (n := ∞)).mdifferentiableOn (by simp)
  exact ⟨he.mfderiv (by simp [m60SphereChart] : z ∈ m60SphereChart.symm.source), rfl⟩



theorem m60RoundSphere_gradientFlux (D : LeviCivitaData m60RoundSphereMetric)
    {f : UnitTwoSphere → ℝ} (z : LoopPlane)
    (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f (m60SphereParameter z)) (i : Fin 2) :
    (16 / (‖z‖ ^ 2 + 4) ^ 2) *
        WithLp.ofLp (mpullback (𝓡 2) (𝓡 2) m60SphereParameter (D.gradient f) z) i =
      fderiv ℝ (f ∘ m60SphereParameter) z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  let X := mpullback (𝓡 2) (𝓡 2) m60SphereParameter (D.gradient f) z
  let v := EuclideanSpace.basisFun (Fin 2) ℝ i
  have hi := m60SphereParameter_mfderiv_isInvertible z
  have hinner : m60RoundSphereMetric.inner (m60SphereParameter z)
      (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z X)
      (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z v) =
      (16 / (‖z‖ ^ 2 + 4) ^ 2) * WithLp.ofLp X i := by
    rw [m60RoundSphereMetric_inner, m60SphereParameter_inner]
    simp [v, EuclideanSpace.inner_single_right]
  have hchain := congrArg (fun L => L v) (mvfderiv_comp z hf
    (m60SphereParameter_contMDiff.mdifferentiable (by simp) z))
  calc
    _ = m60RoundSphereMetric.inner (m60SphereParameter z)
        (D.gradient f (m60SphereParameter z))
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z v) := by
      rw [← hinner]
      exact congrArg (fun W => m60RoundSphereMetric.inner (m60SphereParameter z) W
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z v)) (hi.self_apply_inverse _)
    _ = mvfderiv (𝓡 2) f (m60SphereParameter z)
        (mfderiv (𝓡 2) (𝓡 2) m60SphereParameter z v) := D.inner_gradient _ _ _
    _ = mvfderiv (𝓡 2) (f ∘ m60SphereParameter) z v := hchain.symm
    _ = _ := by rw [mvfderiv, mfderiv_eq_fderiv]; rfl




theorem m60RoundSphere_laplacian_stereographic (D : LeviCivitaData m60RoundSphereMetric)
    {f : UnitTwoSphere → ℝ} (z : LoopPlane)
    (hf : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ f (m60SphereParameter z)) :
    (16 / (‖z‖ ^ 2 + 4) ^ 2) * D.laplacian f (m60SphereParameter z) =
      ∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ (f ∘ m60SphereParameter) y
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  have h := D.density_mul_laplacian_eq_coordinate_divergence m60SphereChart.symm
    (by rw [m60SphereChart_eq_chartAt]; exact contMDiffOn_chart_symm)
    (by rw [m60SphereChart_eq_chartAt]; exact contMDiffOn_chart)
    (by simp [m60SphereChart] : z ∈ m60SphereChart.symm.source) hf
  change m60RoundSphereMetric.pullbackVolumeDensity m60SphereParameter z *
    D.laplacian f (m60SphereParameter z) =
    ∑ i : Fin 2, fderiv ℝ (fun y =>
      m60RoundSphereMetric.pullbackVolumeDensity m60SphereParameter y *
        WithLp.ofLp (mpullback (𝓡 2) (𝓡 2) m60SphereParameter (D.gradient f) y) i) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i) at h
  rw [m60RoundSphereMetric_pullbackVolumeDensity] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  have hfe := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have heq : (fun y => m60RoundSphereMetric.pullbackVolumeDensity m60SphereParameter y *
      WithLp.ofLp (mpullback (𝓡 2) (𝓡 2) m60SphereParameter (D.gradient f) y) i) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ (f ∘ m60SphereParameter) y
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
    filter_upwards [m60SphereParameter_contMDiff.continuous.continuousAt.eventually hfe]
      with y hy
    rw [m60RoundSphereMetric_pullbackVolumeDensity]
    exact m60RoundSphere_gradientFlux D y (hy.mdifferentiableAt (by simp)) i
  rw [heq.fderiv_eq]

end PoincareConjecture
