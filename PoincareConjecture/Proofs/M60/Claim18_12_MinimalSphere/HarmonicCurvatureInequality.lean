import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.HarmonicSphereCharts
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.PoleExtension
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.CurvatureIntegralBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem m60Sphere_logConformalFactor_curvature_inequality
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (S : LeviCivitaData m60RoundSphereMetric) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f) (hc : M60WeaklyConformal g f)
    (hharm : M60SphereChartHarmonic g f) (z : LoopPlane)
    (hz : 0 < m60SphereConformalFactor g f (m60SphereParameter z)) :
    2 - 2 * m60SphereCurvatureContribution D f (m60SphereParameter z) ≤
      S.laplacian (fun p => Real.log (m60SphereConformalFactor g f p))
        (m60SphereParameter z) := by
  have hσ : 0 < 16 / (‖z‖ ^ 2 + 4) ^ 2 := by positivity
  have ha : 0 < m60SphereAreaDensity g f z := by
    rw [m60SphereAreaDensity_eq_conformalFactor_mul g f (hf.of_le (by simp)) hc]
    exact mul_pos hz hσ
  have hplane := m60Sphere_logAreaDensity_curvature_inequality D hD f hf hc hharm z ha
  have hround := m60Sphere_logConformalFactor_laplacian S g f hf hc z hz
  apply (mul_le_mul_iff_right₀ hσ).mp
  nlinarith

theorem m60SphereConformalFactor_curvature_inequality
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (S : LeviCivitaData m60RoundSphereMetric) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f) (hc : M60WeaklyConformal g f)
    (hharm : M60SphereChartHarmonic g f) :
    ∀ p, 0 < m60SphereConformalFactor g f p →
      M04.scalarGradientSq m60RoundSphereMetric (m60SphereConformalFactor g f) p /
        m60SphereConformalFactor g f p + 2 * m60SphereConformalFactor g f p -
        2 * m60SphereConformalFactor g f p * m60SphereCurvatureContribution D f p ≤
          S.laplacian (m60SphereConformalFactor g f) p := by
  have hq := m60SphereConformalFactor_contMDiff g f hf hc
  apply m60RoundSphere_extend_regular_inequality S hq
    (m60SphereCurvatureContribution_contMDiff D hD f hf hc).continuous
  intro p hp hpos
  have hsource : p ∈ m60SphereChart.source := by simpa [m60SphereChart] using hp
  have hparameter : m60SphereParameter (m60SphereChart p) = p :=
    m60SphereChart.left_inv hsource
  have hlog := m60Sphere_logConformalFactor_curvature_inequality D hD S f hf hc hharm
    (m60SphereChart p) (by simpa only [hparameter] using hpos)
  rw [hparameter] at hlog
  have hchain := M60.laplacian_log_add S hq 0 p (by simpa only [add_zero] using hpos)
  simp only [add_zero] at hchain
  rw [hchain] at hlog
  have hdiv : 2 - 2 * m60SphereCurvatureContribution D f p +
      M04.scalarGradientSq m60RoundSphereMetric (m60SphereConformalFactor g f) p /
        (m60SphereConformalFactor g f p) ^ 2 ≤
      S.laplacian (m60SphereConformalFactor g f) p / m60SphereConformalFactor g f p := by
    linarith
  have hmul := (le_div_iff₀ hpos).mp hdiv
  convert! hmul using 1
  field_simp
  ring

theorem m60SphereRicciTrace_integral_lower_bound_of_harmonic
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (S : LeviCivitaData m60RoundSphereMetric) (f : UnitTwoSphere → M)
    (hf : M60BranchedMinimalSphere g f) (hharm : M60SphereChartHarmonic g f)
    (ρ : ℝ) (hρ : ∀ p, ρ ≤ D.scalarCurvature (f p)) :
    4 * Real.pi + (ρ / 2) * m60SphereArea g f ≤
      ∫ z : LoopPlane, m60SphereRicciTraceDensity D f z := by
  exact m60SphereRicciTrace_integral_lower_bound_of_differential_inequality D hD S f hf
    (m60SphereConformalFactor_curvature_inequality D hD S f hf.smooth hf.weakly_conformal hharm)
    ρ hρ

end PoincareConjecture
