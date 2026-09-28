import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMetricMajorant
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ProductMovingEnergyVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ProductOrthogonalSectional
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusCurvatureFlux
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusPeriodicVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64CircleProductAnnulus_forward_of_curvature_motion
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n) (hcirc : 0 < circumference)
    {t : ℝ} (ht : t ∈ Ioo a b) {c0 c1 : ℝ → P.charts.Point}
    (A : M64Annulus (P.flow.metric t) c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (P.flow.metric t) A.map p 0 0 = m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m60EnergyDensity (P.flow.metric t) A.map (annulusPoint x 0))
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m60EnergyDensity (P.flow.metric t) A.map (annulusPoint x 1))
    {v : ℝ × LoopPlane → P.charts.Point} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hDU : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 (n + 1)) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hbase : ∀ p, v (0, p) = A.map p)
    (hperiodic : ∀ r x s, v (r, annulusPoint (x + curvePeriod) s) =
      v (r, annulusPoint x s))
    (hvelocity0 : ∀ x, curveVelocity (fun r => v (r, annulusPoint x 0)) 0 =
      m62CurvatureVector P.flow (fun y _ => c0 y) t x)
    (hvelocity1 : ∀ x, curveVelocity (fun r => v (r, annulusPoint x 1)) 0 =
      m62CurvatureVector P.flow (fun y _ => c1 y) t x) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      m64AnnulusArea (P.flow.metric (t + h)) (fun p => v (h, p)) ≤
        A.area + h * ((2 * (n : ℝ) - 1) * K * A.area + eta) := by
  let : Fact (0 < circumference) := ⟨hcirc⟩
  let E := fun q : ℝ × LoopPlane =>
    m60EnergyDensity (P.flow.metric t) (fun z => v (q.1, z)) q.2
  let H := fun q : ℝ × LoopPlane =>
    m60EnergyDensity (P.flow.metric (t + q.1)) (fun z => v (q.1, z)) q.2
  let d := ∫ p in m64AnnulusDomain, fderiv ℝ H (0, p) (1, 0)
  let flux := ∫ x in Icc (0 : ℝ) curvePeriod,
    m64MovingAnnulusCurrent (P.flow.metric t) v 1 (0, annulusPoint x 1) -
      m64MovingAnnulusCurrent (P.flow.metric t) v 1 (0, annulusPoint x 0)
  have hsec := m64CircleProduct_conformal_annulus_sectional_le
    P t A hO hdom hA hconformal hK hcurv
  have hflux : flux ≤ K * A.area := m64Annulus_curvature_motion_current_flux_le
    P.flow A hminimum hconformal hO hdom hA hK hsec hlower hupper
    hepsilon hU hDU hv hbase hvelocity0 hvelocity1
  have hfrozen := (m64AnnulusEnergy_hasDerivAt_of_local_smooth_variation
    (P.flow.metric t) hepsilon hU hDU hv).2
  have hboundary := (m64Annulus_periodic_first_variation_of_conformal_minimum
    (P.flow.connection t) A hminimum hconformal hepsilon hU hDU hv hbase hperiodic).1
  have hfrozen_value : (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) = flux :=
    hfrozen.unique hboundary
  have hcenter : (∫ p in m64AnnulusDomain, E (0, p)) = A.area := by
    change (∫ p in m64AnnulusDomain,
      m60EnergyDensity (P.flow.metric t) (fun z => v (0, z)) p) = A.area
    rw [funext hbase]
    apply integral_congr_ae
    filter_upwards [hconformal] with p hp
    exact (m60AreaDensity_eq_energyDensity_of_gram
      (P.flow.metric t) A.map p hp.1 hp.2).symm
  have hbound := m64CircleProduct_annulus_energy_derivative_le
    P hn ht hepsilon hU hDU hv hK hcurv
  change d ≤ (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) +
    2 * ((n : ℝ) - 1) * K * (∫ p in m64AnnulusDomain, E (0, p)) at hbound
  rw [hfrozen_value, hcenter] at hbound
  have hd : d ≤ (2 * (n : ℝ) - 1) * K * A.area := by nlinarith
  have hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (P.flow.metric t) (fun z => v (0, z)) p 0 0 =
        m60AreaGram (P.flow.metric t) (fun z => v (0, z)) p 1 1 ∧
      m60AreaGram (P.flow.metric t) (fun z => v (0, z)) p 0 1 = 0 :=
    (funext hbase).symm ▸ hconformal
  have hmajor := m64AnnulusArea_forward_majorant_of_conformal_moving_metric
    P.flow ht hepsilon hU hDU hv hconf
  change ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
    m64AnnulusArea (P.flow.metric (t + h)) (fun p => v (h, p)) ≤
      m64AnnulusArea (P.flow.metric t) (fun p => v (0, p)) + h * (d + eta) at hmajor
  rw [funext hbase] at hmajor
  intro eta heta
  filter_upwards [hmajor eta heta, self_mem_nhdsWithin] with h hh hpos
  apply hh.trans
  change A.area + h * (d + eta) ≤ _
  nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hd)]

end PoincareConjecture
