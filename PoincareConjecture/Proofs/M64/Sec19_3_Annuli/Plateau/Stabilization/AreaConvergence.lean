import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.RadialGram
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusWeakMinimizer












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [CompactSpace M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem auxiliaryCircle_radial_annulus_area_bound
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric time) c0 c1) (delta : ℝ) :
    ∃ B : M64Annulus (P.flow.metric time)
      (auxiliaryCircleSection P (P.circle.quotient 0) ∘ c0)
      (auxiliaryCircleSection P (P.circle.quotient delta) ∘ c1),
      B.map = auxiliaryCircleRadialLift P A.map delta ∧
        B.area ≤ A.area + |delta| * (volume.real m64AnnulusDomain +
          ∫ z in m64AnnulusDomain, m60EnergyDensity (F.metric time) A.map z) := by
  obtain ⟨B, hmap⟩ := auxiliaryCircle_radial_annulus P time A delta
  have hE := A.energy_integrable
  have hconst : IntegrableOn (fun _ : LoopPlane => (1 : ℝ)) m64AnnulusDomain volume :=
    integrableOn_const m64AnnulusDomain_volume_ne_top
  have herror : IntegrableOn (fun z => |delta| *
      (1 + m60EnergyDensity (F.metric time) A.map z)) m64AnnulusDomain volume :=
    (hconst.add hE).const_mul |delta|
  have hbound : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      m60AreaDensity (P.flow.metric time) B.map z ≤
        m60AreaDensity (F.metric time) A.map z +
          |delta| * (1 + m60EnergyDensity (F.metric time) A.map z) := by
    filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet,
      ae_restrict_of_ae A.ae_manifold_differentiable] with z hz hdiff
    rw [hmap]
    exact auxiliaryCircle_radial_density_le_energy_error P time delta (hdiff hz)
  refine ⟨B, hmap, ?_⟩
  calc
    B.area ≤ ∫ z in m64AnnulusDomain,
        (m60AreaDensity (F.metric time) A.map z +
          |delta| * (1 + m60EnergyDensity (F.metric time) A.map z)) :=
      integral_mono_ae B.area_integrable (A.area_integrable.add herror) hbound
    _ = A.area + |delta| * (volume.real m64AnnulusDomain +
        ∫ z in m64AnnulusDomain, m60EnergyDensity (F.metric time) A.map z) := by
      rw [integral_add A.area_integrable herror, integral_const_mul,
        integral_add hconst hE]
      simp only [integral_const, Measure.real, smul_eq_mul, mul_one,
        Measure.restrict_apply_univ, M64Annulus.area, m64AnnulusArea]

omit [CompactSpace M] in


theorem auxiliaryCircle_leastArea_le_lifted_leastArea
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric time) c0 c1) (delta : ℝ) :
    m64LeastAnnulusArea (F.metric time) c0 c1 ≤
      m64LeastAnnulusArea (P.flow.metric time)
        (auxiliaryCircleSection P (P.circle.quotient 0) ∘ c0)
        (auxiliaryCircleSection P (P.circle.quotient delta) ∘ c1) := by
  obtain ⟨B, -⟩ := auxiliaryCircle_radial_annulus P time A delta
  have hnonempty := m64AnnulusAreaRange_nonempty B
  have hbounded := m64AnnulusAreaRange_bddBelow (P.flow.metric time)
    (auxiliaryCircleSection P (P.circle.quotient 0) ∘ c0)
    (auxiliaryCircleSection P (P.circle.quotient delta) ∘ c1)
  apply (isGLB_csInf hnonempty hbounded).2
  rintro _ ⟨C, rfl⟩
  obtain ⟨-, D, -, -, -, harea⟩ := m64ProjectedAnnulus_of_annulus P time _ _ C
  exact (m64LeastAnnulusArea_le_annulus D).trans harea



theorem auxiliaryCircle_lifted_leastArea_error
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric time) c0 c1) (delta : ℝ) :
    m64LeastAnnulusArea (P.flow.metric time)
        (auxiliaryCircleSection P (P.circle.quotient 0) ∘ c0)
        (auxiliaryCircleSection P (P.circle.quotient delta) ∘ c1) ≤
      A.area + |delta| * (volume.real m64AnnulusDomain +
        ∫ z in m64AnnulusDomain, m60EnergyDensity (F.metric time) A.map z) := by
  obtain ⟨B, -, harea⟩ := auxiliaryCircle_radial_annulus_area_bound P time A delta
  exact (m64LeastAnnulusArea_le_annulus B).trans harea



theorem auxiliaryCircle_lifted_leastArea_tendsto
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric time) c0 c1) :
    Tendsto (fun delta : ℝ => m64LeastAnnulusArea (P.flow.metric time)
      (auxiliaryCircleSection P (P.circle.quotient 0) ∘ c0)
      (auxiliaryCircleSection P (P.circle.quotient delta) ∘ c1)) (𝓝 0)
      (𝓝 (m64LeastAnnulusArea (F.metric time) c0 c1)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨C, hC⟩ := m64LeastAnnulusArea_near_minimizer A (half_pos hepsilon)
  let K := volume.real m64AnnulusDomain +
    ∫ z in m64AnnulusDomain, m60EnergyDensity (F.metric time) C.map z
  have hK : 0 ≤ K := add_nonneg ENNReal.toReal_nonneg
    (integral_nonneg (fun z => m60EnergyDensity_nonneg (F.metric time) C.map z))
  have hK1 : 0 < K + 1 := by linarith
  have hsmall : ∀ᶠ delta : ℝ in 𝓝 0, |delta| < (epsilon / 2) / (K + 1) := by
    have hpos := div_pos (half_pos hepsilon) hK1
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with delta hdelta
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hdelta
  filter_upwards [hsmall] with delta hdelta
  have hupper := auxiliaryCircle_lifted_leastArea_error P time C delta
  have hlower := auxiliaryCircle_leastArea_le_lifted_leastArea P time A delta
  have herror : |delta| * K < epsilon / 2 := by
    have hlt := (lt_div_iff₀ hK1).mp hdelta
    nlinarith [abs_nonneg delta]
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
  change _ ≤ C.area + |delta| * K at hupper
  linarith



theorem auxiliaryCircle_radial_annuli_area_tendsto
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric time) c0 c1) :
    ∃ B : ∀ delta : ℝ, M64Annulus (P.flow.metric time)
      (auxiliaryCircleSection P (P.circle.quotient 0) ∘ c0)
      (auxiliaryCircleSection P (P.circle.quotient delta) ∘ c1),
      (∀ delta, (B delta).map = auxiliaryCircleRadialLift P A.map delta) ∧
        Tendsto (fun delta => (B delta).area) (𝓝 0) (𝓝 A.area) := by
  choose B hmap hbound using (fun delta => auxiliaryCircle_radial_annulus_area_bound P time A delta)
  refine ⟨B, hmap, ?_⟩
  let K := volume.real m64AnnulusDomain +
    ∫ z in m64AnnulusDomain, m60EnergyDensity (F.metric time) A.map z
  have hupper : Tendsto (fun delta : ℝ => A.area + |delta| * K) (𝓝 0) (𝓝 A.area) := by
    have hcont : Continuous (fun delta : ℝ => A.area + |delta| * K) := by fun_prop
    simpa only [abs_zero, zero_mul, add_zero] using hcont.tendsto 0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper ?_ hbound
  intro delta
  obtain ⟨-, C, hC, -, -, harea⟩ := m64ProjectedAnnulus_of_annulus P time _ _ (B delta)
  have hmapC : C.map = A.map := by
    rw [hC, hmap delta]
    rfl
  have hareaC : C.area = A.area := by
    unfold M64Annulus.area m64AnnulusArea
    rw [hmapC]
  exact hareaC.symm.le.trans harea

end PoincareConjecture.M64
