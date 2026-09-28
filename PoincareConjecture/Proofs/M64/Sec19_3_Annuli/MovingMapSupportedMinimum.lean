import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapSupportedFlux
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapSupportedVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64Annulus_supported_chart_flux_of_conformal_minimum
    (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (b : M) {O : Set LoopPlane} (hO : IsOpen O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hchart : MapsTo A.map O (extChartAt (𝓡 n) b).source)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (hVO : tsupport V ⊆ O)
    (hseam :
      let u := (extChartAt (𝓡 n) b) ∘ A.map
      let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
      ∀ s ∈ Icc (0 : ℝ) 1,
        B (u (annulusPoint curvePeriod s)) (V (annulusPoint curvePeriod s))
          (fderiv ℝ u (annulusPoint curvePeriod s) (EuclideanSpace.single (0 : Fin 2) 1)) =
        B (u (annulusPoint 0 s)) (V (annulusPoint 0 s))
          (fderiv ℝ u (annulusPoint 0 s) (EuclideanSpace.single (0 : Fin 2) 1))) :
    let u := (extChartAt (𝓡 n) b) ∘ A.map
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    (∫ p in m64AnnulusDomain, ∑ i : Fin 2, B (u p)
      (covDerivAlong (christoffelBilinear B) u V (EuclideanSpace.basisFun (Fin 2) ℝ i) p)
      (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i))) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        B (u (annulusPoint x 1)) (V (annulusPoint x 1))
          (fderiv ℝ u (annulusPoint x 1) (EuclideanSpace.single (1 : Fin 2) 1)) -
        B (u (annulusPoint x 0)) (V (annulusPoint x 0))
          (fderiv ℝ u (annulusPoint x 0) (EuclideanSpace.single (1 : Fin 2) 1)) := by
  let c := extChartAt (𝓡 n) b
  let u := c ∘ A.map
  let B := g.pullbackCoefficients c.symm
  let Gamma := christoffelBilinear B
  let C := M60.mapConnectionCoefficients Gamma u
  let G := fun p => B (u p)
  let e0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let e1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  let W0 := fun p => fderiv ℝ u p e0
  let W1 := fun p => fderiv ℝ u p e1
  have hu : ContDiffOn ℝ ∞ u O := by
    intro p hp
    have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (A.map p) :=
      contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hchart hp)
    exact (contMDiffAt_iff_contDiffAt.mp
      (hc.comp p (hA.contMDiffAt (hO.mem_nhds hp)))).contDiffWithinAt
  have hB (p : LoopPlane) (hp : p ∈ O) : ContDiffAt ℝ ∞ B (u p) :=
    (g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (c.map_source (hchart hp)))
  have hGamma (p : LoopPlane) (hp : p ∈ O) : ContDiffAt ℝ ∞ Gamma (u p) :=
    contDiffAt_christoffelBilinear (hB p hp)
      (g.isInvertible_chartCoefficients b (c.map_source (hchart hp)))
  have hC : ContDiffOn ℝ ∞ C O := by
    intro p hp
    exact (M60.contDiffAt_mapConnectionCoefficients (hGamma p hp)
      (hu.contDiffAt (hO.mem_nhds hp))).contDiffWithinAt
  have hG : ContDiffOn ℝ ∞ G O := by
    intro p hp
    exact ((hB p hp).comp p (hu.contDiffAt (hO.mem_nhds hp))).contDiffWithinAt
  have hW0 : ContDiffOn ℝ ∞ W0 O :=
    (hu.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hW1 : ContDiffOn ℝ ∞ W1 O :=
    (hu.fderiv_of_isOpen hO (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hcompat (p : LoopPlane) (hp : p ∈ O) (d : LoopPlane)
      (a b : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun q => G q a b) p d = G p (C p d a) b + G p a (C p d b) := by
    have hm := fderiv_metricAlong (G := B) (Γ := Gamma) (u := u)
      (V := fun _ : LoopPlane => a) (W := fun _ : LoopPlane => b) (p := p)
      (isMetricCompatibleAt_chartCoefficients g _ (c.map_source (hchart hp)))
      ((hB p hp).differentiableAt (by simp))
      ((hu.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp))
      (differentiableAt_const a) (differentiableAt_const b) d
    simpa only [G, C, M60.mapConnectionCoefficients, covDerivAlong_def,
      fderiv_const_apply, zero_apply, zero_add, ContinuousLinearMap.comp_apply] using hm
  have hflux := m64Annulus_covariant_boundary_flux_supported hO hC hG hV.contDiffOn
    hW0 hW1 hVc hVO hcompat hseam
  have hharm := m64Annulus_chart_harmonic_of_conformal_minimum A hminimum hconformal b
    (hO.inter isOpen_m64AnnulusInterior) inter_subset_right (hA.mono inter_subset_left)
    (fun _ hp => hchart hp.1)
  have hrestrict : volume.restrict (interior m64AnnulusDomain) =
      volume.restrict m64AnnulusInterior := by
    rw [← m64Annulus_restrict_closed_eq_interior]
    exact Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior
  have htension : (∫ p in interior m64AnnulusDomain, G p (V p)
      (Poincare.Riemannian.RadialTransport.covariantDerivative C W0 p e0 +
        Poincare.Riemannian.RadialTransport.covariantDerivative C W1 p e1)) = 0 := by
    rw [hrestrict]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem isOpen_m64AnnulusInterior.measurableSet] with p hp
    by_cases hs : p ∈ tsupport V
    · have hz : covDerivAlong Gamma u W0 e0 p + covDerivAlong Gamma u W1 e1 p = 0 := by
        simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_apply] using
          hharm p ⟨hVO hs, hp⟩
      change G p (V p) (covDerivAlong Gamma u W0 e0 p +
        covDerivAlong Gamma u W1 e1 p) = 0
      rw [hz, map_zero]
    · simp [image_eq_zero_of_notMem_tsupport hs]
  rw [htension, add_zero] at hflux
  change (∫ p in m64AnnulusDomain, ∑ i : Fin 2, B (u p)
    (covDerivAlong Gamma u V (EuclideanSpace.basisFun (Fin 2) ℝ i) p)
    (fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i))) = _
  rw [m64Annulus_restrict_closed_eq_interior]
  simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_apply,
    G, C, W0, W1, e0, e1, M60.covariantDerivative_mapConnectionCoefficients] using hflux

theorem m64Annulus_supported_chart_first_variation_of_conformal_minimum
    (A : M64Annulus g c0 c1)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g A.map p 0 0 = m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    (b : M) {O : Set LoopPlane} (hO : IsOpen O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    (hchart : MapsTo A.map O (extChartAt (𝓡 n) b).source)
    (V : LoopPlane → EuclideanSpace ℝ (Fin n)) (hV : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport V) (hVO : tsupport V ⊆ O)
    (hseam :
      let u := (extChartAt (𝓡 n) b) ∘ A.map
      let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
      ∀ s ∈ Icc (0 : ℝ) 1,
        B (u (annulusPoint curvePeriod s)) (V (annulusPoint curvePeriod s))
          (fderiv ℝ u (annulusPoint curvePeriod s) (EuclideanSpace.single (0 : Fin 2) 1)) =
        B (u (annulusPoint 0 s)) (V (annulusPoint 0 s))
          (fderiv ℝ u (annulusPoint 0 s) (EuclideanSpace.single (0 : Fin 2) 1)))
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ O))
    (hcoord : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ p ∈ O,
      v (s, p) ∈ (extChartAt (𝓡 n) b).source ∧
        extChartAt (𝓡 n) b (v (s, p)) =
          extChartAt (𝓡 n) b (A.map p) + s • V p)
    (hfix : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ p ∉ tsupport V, v (s, p) = A.map p)
    (hint : ∀ s ∈ Ioo (-epsilon) epsilon,
      IntegrableOn (m60EnergyDensity g (fun p => v (s, p))) m64AnnulusDomain volume) :
    let u := (extChartAt (𝓡 n) b) ∘ A.map
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
    let flux := ∫ x in Icc (0 : ℝ) curvePeriod,
      B (u (annulusPoint x 1)) (V (annulusPoint x 1))
        (fderiv ℝ u (annulusPoint x 1) (EuclideanSpace.single (1 : Fin 2) 1)) -
      B (u (annulusPoint x 0)) (V (annulusPoint x 0))
        (fderiv ℝ u (annulusPoint x 0) (EuclideanSpace.single (1 : Fin 2) 1))
    HasDerivAt (fun s => ∫ p in m64AnnulusDomain,
      m60EnergyDensity g (fun z => v (s, z)) p) flux 0 ∧
      ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
        m64AnnulusArea g (fun p => v (h, p)) ≤ A.area + h * (flux + eta) := by
  let u := (extChartAt (𝓡 n) b) ∘ A.map
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
  let flux := ∫ x in Icc (0 : ℝ) curvePeriod,
    B (u (annulusPoint x 1)) (V (annulusPoint x 1))
      (fderiv ℝ u (annulusPoint x 1) (EuclideanSpace.single (1 : Fin 2) 1)) -
    B (u (annulusPoint x 0)) (V (annulusPoint x 0))
      (fderiv ℝ u (annulusPoint x 0) (EuclideanSpace.single (1 : Fin 2) 1))
  let energy := fun s => ∫ p in m64AnnulusDomain, m60EnergyDensity g (fun z => v (s, z)) p
  have hflux := m64Annulus_supported_chart_flux_of_conformal_minimum
    A hminimum hconformal b hO hA hchart V hV hVc hVO hseam
  have hd := (m64AnnulusEnergy_hasDerivAt_of_boundary_supported_chart
    g b A.map hO hA hchart V hV hVc hVO hepsilon hv hcoord hfix hint).2
  have hderiv : HasDerivAt energy flux 0 := by
    rw [hflux] at hd
    exact hd
  refine ⟨hderiv, ?_⟩
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hmapzero : (fun p => v (0, p)) = A.map := by
    ext p
    by_cases hp : p ∈ tsupport V
    · apply (extChartAt (𝓡 n) b).injOn (hcoord 0 hzero p (hVO hp)).1 (hchart (hVO hp))
      simpa only [zero_smul, add_zero] using (hcoord 0 hzero p (hVO hp)).2
    · exact hfix 0 hzero p hp
  have hcenter : energy 0 = A.area := by
    simp only [energy, hmapzero]
    exact m64Annulus_energy_eq_area_of_ae_conformal A hconformal
  have hupper (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      m64AnnulusArea g (fun p => v (s, p)) ≤ energy s :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun p => m60AreaDensity_nonneg g (fun p => v (s, p)) p)
      (hint s hs)
      (Eventually.of_forall fun p => m60AreaDensity_le_energyDensity g (fun p => v (s, p)) p)
  have hquot : Tendsto (fun h => (energy h - energy 0) / h) (𝓝[>] 0) (𝓝 flux) := by
    simpa only [zero_add, smul_eq_mul, ← div_eq_inv_mul] using hderiv.tendsto_slope_zero_right
  intro eta heta
  have hev := hquot.eventually (Iio_mem_nhds (lt_add_of_pos_right flux heta))
  have htime : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-epsilon) epsilon :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hzero)
  filter_upwards [hev, htime, self_mem_nhdsWithin] with h hh htime hpos
  have hdiff := (div_le_iff₀ hpos).mp hh.le
  rw [hcenter] at hdiff
  exact (hupper h htime).trans (by linarith)

end PoincareConjecture
