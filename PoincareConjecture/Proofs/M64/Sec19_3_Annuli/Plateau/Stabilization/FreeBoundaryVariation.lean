import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.WeightedMetricVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.CircleCurvatureNorm
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeProductVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_free_modulus_sharp_variation
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (hn : 1 ≤ n)
    {c0 c1 : ℝ → ℝ → Q.charts.Point}
    (hc0 : M63C2ShrinkingCurveOn Q.flow c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn Q.flow c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (Q.flow.metric t)
      ((fun x => c0 x t) ∘ sigma0.map) ((fun x => c1 x t) ∘ sigma1.map))
    {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea (Q.flow.metric t)
      (fun x => c0 x t) (fun x => c1 x t))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (Q.flow.metric t) A.map p 0 0 =
          r⁻¹ * m60AreaGram (Q.flow.metric t) A.map p 1 1 ∧
        m60AreaGram (Q.flow.metric t) A.map p 0 1 = 0)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ A.map O)
    {K : ℝ} (hK : 0 ≤ K)
    (hcurv : ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ K)
    {v : ℝ × LoopPlane → Q.charts.Point} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hDU : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 ((n + 1) + 1)) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hbase : ∀ p, v (0, p) = A.map p)
    (hperiodic : ∀ z x s, v (z, annulusPoint (x + curvePeriod) s) =
      v (z, annulusPoint x s))
    (hvelocity0 : ∀ x, curveVelocity (fun z => v (z, annulusPoint x 0)) 0 =
      m62CurvatureVector Q.flow c0 t (sigma0.map x))
    (hvelocity1 : ∀ x, curveVelocity (fun z => v (z, annulusPoint x 1)) 0 =
      m62CurvatureVector Q.flow c1 t (sigma1.map x)) :
    let H := fun q : ℝ × LoopPlane =>
      m64ModulusEnergyDensity (Q.flow.metric (t + q.1)) r (fun z => v (q.1, z)) q.2
    (∫ p in m64AnnulusDomain, fderiv ℝ H (0, p) (1, 0)) ≤
        (2 * (n : ℝ) - 1) * K * A.area ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
        m64AnnulusArea (Q.flow.metric (t + h)) (fun p => v (h, p)) ≤
          A.area + h * ((2 * (n : ℝ) - 1) * K * A.area + eta) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  have htcc := Ioo_subset_Icc_self ht
  have hown := m64FreeAnnulus_minimizes_own_boundary
    (m64C2ShrinkingCurves_freeBoundaryAreaTransport Q.flow hc0 hc1 htcc)
    sigma0 sigma1 A hminimum
  let E := fun q : ℝ × LoopPlane =>
    m64ModulusEnergyDensity (Q.flow.metric t) r (fun z => v (q.1, z)) q.2
  let H := fun q : ℝ × LoopPlane =>
    m64ModulusEnergyDensity (Q.flow.metric (t + q.1)) r (fun z => v (q.1, z)) q.2
  let d := ∫ p in m64AnnulusDomain, fderiv ℝ H (0, p) (1, 0)
  let flux := r⁻¹ * ∫ x in Icc (0 : ℝ) curvePeriod,
    m64MovingAnnulusCurrent (Q.flow.metric t) v 1 (0, annulusPoint x 1) -
      m64MovingAnnulusCurrent (Q.flow.metric t) v 1 (0, annulusPoint x 0)
  have hsec : ∀ p ∈ m64AnnulusInterior,
      (Q.flow.connection t).sectionalCurvature (A.map p)
        (mfderiv (𝓡 2) (𝓡 ((n + 1) + 1)) A.map p (EuclideanSpace.single (0 : Fin 2) 1))
        (mfderiv (𝓡 2) (𝓡 ((n + 1) + 1)) A.map p (EuclideanSpace.single (1 : Fin 2) 1)) ≤
          K := by
    intro p _
    exact (le_abs_self _).trans
      ((auxiliaryCircle_sectional_abs_le P Q t (A.map p) _ _).trans (hcurv (A.map p).1.1))
  have hflux : flux ≤ K * A.area := m64FreeAnnulus_modulus_curvature_motion_current_flux_le
    Q.flow hc0 hc1 htcc sigma0 sigma1 A hr hown hconformal hO hdom hA hK hsec
    hepsilon hU hDU hv hbase hvelocity0 hvelocity1
  have hfrozen := (m64ModulusAnnulusEnergy_hasDerivAt_of_local_smooth_variation
    (Q.flow.metric t) r hepsilon hU hDU hv).2
  have hboundary := m64Annulus_periodic_first_variation_of_modulus_minimum
    (Q.flow.connection t) A hr hown hconformal hepsilon hU hDU hv hbase hperiodic
  have hfrozen_value : (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) = flux :=
    hfrozen.unique hboundary
  have hcenter : (∫ p in m64AnnulusDomain, E (0, p)) = A.area := by
    change (∫ p in m64AnnulusDomain,
      m64ModulusEnergyDensity (Q.flow.metric t) r (fun z => v (0, z)) p) = A.area
    rw [funext hbase]
    exact m64_weightedEnergy_eq_area_of_ae_modulus_conformal A hr hconformal
  have hbound := auxiliaryCircle_annulus_modulusEnergy_derivative_le
    P Q hn ht hr hepsilon hU hDU hv hK hcurv
  change d ≤ (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) +
    2 * ((n : ℝ) - 1) * K * (∫ p in m64AnnulusDomain, E (0, p)) at hbound
  rw [hfrozen_value, hcenter] at hbound
  have hd : d ≤ (2 * (n : ℝ) - 1) * K * A.area := by nlinarith
  refine ⟨hd, ?_⟩
  have hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram (Q.flow.metric t) (fun z => v (0, z)) p 0 0 =
          r⁻¹ * m60AreaGram (Q.flow.metric t) (fun z => v (0, z)) p 1 1 ∧
        m60AreaGram (Q.flow.metric t) (fun z => v (0, z)) p 0 1 = 0 :=
    (funext hbase).symm ▸ hconformal
  have hmajor := m64AnnulusArea_forward_majorant_of_modulus_conformal_moving_metric
    Q.flow r ht hepsilon hU hDU hv hr hconf
  change ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
    m64AnnulusArea (Q.flow.metric (t + h)) (fun p => v (h, p)) ≤
      m64AnnulusArea (Q.flow.metric t) (fun p => v (0, p)) + h * (d + eta) at hmajor
  rw [funext hbase] at hmajor
  intro eta heta
  filter_upwards [hmajor eta heta, self_mem_nhdsWithin] with h hh hpos
  apply hh.trans
  change A.area + h * (d + eta) ≤ _
  nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hd)]

end PoincareConjecture.M64
