import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RicciTraceTransport
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RegularizedCurvatureIntegral










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}




theorem m60SphereRicciTrace_integral_lower_bound_of_curvature
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hc : M60WeaklyConformal g f) (ρ : ℝ)
    (hρ : ∀ p, ρ ≤ D.scalarCurvature (f p))
    (hcurv : 4 * Real.pi ≤ ∫ p, m60SphereCurvatureContribution D f p
      ∂m60RoundSphereMetric.volumeMeasure) :
    4 * Real.pi + (ρ / 2) * m60SphereArea g f ≤
      ∫ z : LoopPlane, m60SphereRicciTraceDensity D f z := by
  let q := m60SphereConformalFactor g f
  have hq : Integrable q m60RoundSphereMetric.volumeMeasure :=
    m60SphereConformalFactor_integrable g f hf hc
  have hs : Integrable (fun p => (D.scalarCurvature (f p) / 2) * q p)
      m60RoundSphereMetric.volumeMeasure :=
    (((m60ScalarCurvature_contMDiff D hD).comp hf).continuous.div_const 2 |>.mul
      (m60SphereConformalFactor_contMDiff g f hf hc).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hk := m60SphereCurvatureContribution_integrable D hD f hf hc
  have hb := integral_mono (hq.const_mul (ρ / 2)) hs (fun p =>
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hρ p) (by norm_num))
      (m60SphereConformalFactor_nonneg g f p))
  rw [integral_const_mul] at hb
  have hid : m60SphereIntrinsicRicciTrace D f =
      (fun p => (D.scalarCurvature (f p) / 2) * q p + m60SphereCurvatureContribution D f p) := by
    funext p
    dsimp [m60SphereCurvatureContribution, q]
    ring
  rw [m60SphereRicciTrace_integral_eq_intrinsic D hD f hf hc, hid,
    integral_add hs hk, m60SphereArea_eq_integral_conformalFactor g f hf hc]
  change 4 * Real.pi + (ρ / 2) * (∫ p, q p ∂m60RoundSphereMetric.volumeMeasure) ≤ _
  linarith




theorem m60SphereRicciTrace_integral_lower_bound_of_differential_inequality
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (S : LeviCivitaData m60RoundSphereMetric) (f : UnitTwoSphere → M)
    (hf : M60BranchedMinimalSphere g f)
    (hreg : ∀ p, 0 < m60SphereConformalFactor g f p →
      M04.scalarGradientSq m60RoundSphereMetric (m60SphereConformalFactor g f) p /
        m60SphereConformalFactor g f p + 2 * m60SphereConformalFactor g f p -
        2 * m60SphereConformalFactor g f p * m60SphereCurvatureContribution D f p ≤
          S.laplacian (m60SphereConformalFactor g f) p)
    (ρ : ℝ) (hρ : ∀ p, ρ ≤ D.scalarCurvature (f p)) :
    4 * Real.pi + (ρ / 2) * m60SphereArea g f ≤
      ∫ z : LoopPlane, m60SphereRicciTraceDensity D f z := by
  apply m60SphereRicciTrace_integral_lower_bound_of_curvature D hD f hf.smooth
    hf.weakly_conformal ρ hρ
  exact m60RoundSphere_curvature_integral_of_differential_inequality S
    (m60SphereConformalFactor_contMDiff g f hf.smooth hf.weakly_conformal)
    (m60SphereConformalFactor_nonneg g f)
    (m60SphereConformalFactor_ae_pos g f hf.weakly_conformal hf.finite_branch_set)
    (m60SphereCurvatureContribution_integrable D hD f hf.smooth hf.weakly_conformal) hreg

end PoincareConjecture
