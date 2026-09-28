import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMovingCurvatureFlux
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMovingAnnulusFirstVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ProductOrthogonalSectional

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem m64CircleProductAnnulus_modulus_sharp_variation
    (P : M62.CircleProductData F circumference) (hn : 1 ≤ n) (hcirc : 0 < circumference)
    {t : ℝ} (ht : t ∈ Ioo a b) {c0 c1 : ℝ → P.charts.Point}
    (A : M64Annulus (P.flow.metric t) c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t) c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    (hlower : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m64ModulusEnergyDensity (P.flow.metric t) r A.map (annulusPoint x 0))
    (hupper : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      0 < m64ModulusEnergyDensity (P.flow.metric t) r A.map (annulusPoint x 1))
    {v : ℝ × LoopPlane → P.charts.Point} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hDU : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 (n + 1)) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hbase : ∀ p, v (0, p) = A.map p)
    (hperiodic : ∀ z x s, v (z, annulusPoint (x + curvePeriod) s) =
      v (z, annulusPoint x s))
    (hvelocity0 : ∀ x, curveVelocity (fun z => v (z, annulusPoint x 0)) 0 =
      m62CurvatureVector P.flow (fun y _ => c0 y) t x)
    (hvelocity1 : ∀ x, curveVelocity (fun z => v (z, annulusPoint x 1)) 0 =
      m62CurvatureVector P.flow (fun y _ => c1 y) t x) :
    let H := fun q : ℝ × LoopPlane =>
      m64ModulusEnergyDensity (P.flow.metric (t + q.1)) r (fun z => v (q.1, z)) q.2
    (∫ p in m64AnnulusDomain, fderiv ℝ H (0, p) (1, 0)) ≤
        (2 * (n : ℝ) - 1) * K * A.area ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
        m64AnnulusArea (P.flow.metric (t + h)) (fun p => v (h, p)) ≤
          A.area + h * ((2 * (n : ℝ) - 1) * K * A.area + eta) := by
  let : Fact (0 < circumference) := ⟨hcirc⟩
  let E := fun q : ℝ × LoopPlane =>
    m64ModulusEnergyDensity (P.flow.metric t) r (fun z => v (q.1, z)) q.2
  let H := fun q : ℝ × LoopPlane =>
    m64ModulusEnergyDensity (P.flow.metric (t + q.1)) r (fun z => v (q.1, z)) q.2
  let d := ∫ p in m64AnnulusDomain, fderiv ℝ H (0, p) (1, 0)
  let flux := r⁻¹ * ∫ x in Icc (0 : ℝ) curvePeriod,
    m64MovingAnnulusCurrent (P.flow.metric t) v 1 (0, annulusPoint x 1) -
      m64MovingAnnulusCurrent (P.flow.metric t) v 1 (0, annulusPoint x 0)
  have hsec : ∀ p ∈ m64AnnulusInterior,
      (P.flow.connection t).sectionalCurvature (A.map p)
        (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
        (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤ K := by
    intro p hp
    have hc := (m64Annulus_modulus_conformal_on_domain_of_ae A r hO hdom hA
      hconformal p (m64AnnulusInterior_subset_domain hp)).2
    have ho : (P.flow.metric t).inner (A.map p)
        (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
        (mfderiv (𝓡 2) (𝓡 (n + 1)) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) = 0 := by
      simpa only [m60AreaGram, EuclideanSpace.basisFun_apply] using hc
    exact (le_abs_self _).trans
      (m64CircleProduct_orthogonal_sectional_abs_le P t hK (A.map p)
        (hcurv (A.map p).1) _ _ ho)
  have hflux : flux ≤ K * A.area := m64Annulus_modulus_curvature_motion_current_flux_le
    P.flow A hr hminimum hconformal hO hdom hA hK hsec hlower hupper
    hepsilon hU hDU hv hbase hvelocity0 hvelocity1
  have hfrozen := (m64ModulusAnnulusEnergy_hasDerivAt_of_local_smooth_variation
    (P.flow.metric t) r hepsilon hU hDU hv).2
  have hboundary := m64Annulus_periodic_first_variation_of_modulus_minimum
    (P.flow.connection t) A hr hminimum hconformal hepsilon hU hDU hv hbase hperiodic
  have hfrozen_value : (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) = flux :=
    hfrozen.unique hboundary
  have hcenter : (∫ p in m64AnnulusDomain, E (0, p)) = A.area := by
    change (∫ p in m64AnnulusDomain,
      m64ModulusEnergyDensity (P.flow.metric t) r (fun z => v (0, z)) p) = A.area
    rw [funext hbase]
    exact m64_weightedEnergy_eq_area_of_ae_modulus_conformal A hr hconformal
  have hbound := m64CircleProduct_annulus_modulusEnergy_derivative_le
    P hn ht hr hepsilon hU hDU hv hK hcurv
  change d ≤ (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) +
    2 * ((n : ℝ) - 1) * K * (∫ p in m64AnnulusDomain, E (0, p)) at hbound
  rw [hfrozen_value, hcenter] at hbound
  have hd : d ≤ (2 * (n : ℝ) - 1) * K * A.area := by nlinarith
  refine ⟨hd, ?_⟩
  have hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (P.flow.metric t) (fun z => v (0, z)) p 0 0 =
          r⁻¹ * m60AreaGram (P.flow.metric t) (fun z => v (0, z)) p 1 1 ∧
        m60AreaGram (P.flow.metric t) (fun z => v (0, z)) p 0 1 = 0 :=
    (funext hbase).symm ▸ hconformal
  have hmajor := m64AnnulusArea_forward_majorant_of_modulus_conformal_moving_metric
    P.flow r ht hepsilon hU hDU hv hr hconf
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
