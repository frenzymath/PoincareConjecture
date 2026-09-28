import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates
import PoincareConjecture.Proofs.M60.Mathlib.CompactSupportIntegralDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

theorem m64AnnulusIntegral_hasDerivAt_of_continuous_derivative
    {F F' : ℝ → LoopPlane → ℝ}
    (hF : ∀ s, Continuous (F s))
    (hF' : Continuous (Function.uncurry F'))
    (hdiff : ∀ s p, HasDerivAt (fun r => F r p) (F' s p) s) (t : ℝ) :
    IntegrableOn (F' t) m64AnnulusDomain volume ∧
      HasDerivAt (fun s => ∫ p in m64AnnulusDomain, F s p)
        (∫ p in m64AnnulusDomain, F' t p) t := by
  have hcompact : IsCompact (Icc (t - 1) (t + 1) ×ˢ m64AnnulusDomain) :=
    isCompact_Icc.prod m64AnnulusDomain_isCompact
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hF'.continuousOn
  have hbound : Integrable (fun _ : LoopPlane => max C 0)
      (volume.restrict m64AnnulusDomain) :=
    integrableOn_const m64AnnulusDomain_isCompact.measure_ne_top
  have hFint : IntegrableOn (F t) m64AnnulusDomain volume :=
    (hF t).continuousOn.integrableOn_compact m64AnnulusDomain_isCompact
  have hF'meas : AEStronglyMeasurable (F' t) (volume.restrict m64AnnulusDomain) :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (t - 1) (t + 1)) (bound := fun _ => max C 0)
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) _ hFint hF'meas _ hbound _
  · exact Eventually.of_forall fun s => (hF s).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet] with p hp s hs
    exact (hC (s, p) ⟨⟨hs.1.le, hs.2.le⟩, hp⟩).trans (le_max_left C 0)
  · exact Eventually.of_forall fun p s _ => hdiff s p

theorem m64AnnulusIntegral_hasDerivAt_of_local_continuous_derivative
    {F F' : ℝ → LoopPlane → ℝ} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hF : ∀ s ∈ Ioo (-epsilon) epsilon, ContinuousOn (F s) m64AnnulusDomain)
    (hF' : ContinuousOn (Function.uncurry F')
      (Ioo (-epsilon) epsilon ×ˢ m64AnnulusDomain))
    (hdiff : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ p ∈ m64AnnulusDomain,
      HasDerivAt (fun r => F r p) (F' s p) s) :
    IntegrableOn (F' 0) m64AnnulusDomain volume ∧
      HasDerivAt (fun s => ∫ p in m64AnnulusDomain, F s p)
        (∫ p in m64AnnulusDomain, F' 0 p) 0 := by
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hsmall : Icc (-epsilon / 2) (epsilon / 2) ⊆ Ioo (-epsilon) epsilon := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod m64AnnulusDomain_isCompact).exists_bound_of_continuousOn
    (hF'.mono (prod_mono_left hsmall))
  have hbound : Integrable (fun _ : LoopPlane => max C 0)
      (volume.restrict m64AnnulusDomain) :=
    integrableOn_const m64AnnulusDomain_isCompact.measure_ne_top
  have hFint : IntegrableOn (F 0) m64AnnulusDomain volume :=
    (hF 0 hzero).integrableOn_compact m64AnnulusDomain_isCompact
  have hF'meas : AEStronglyMeasurable (F' 0) (volume.restrict m64AnnulusDomain) :=
    (hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp => ⟨hzero, hp⟩)).aestronglyMeasurable m64AnnulusDomain_measurableSet
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (-epsilon / 2) (epsilon / 2)) (bound := fun _ => max C 0)
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) _ hFint hF'meas _ hbound _
  · filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    exact (hF s hs).aestronglyMeasurable m64AnnulusDomain_measurableSet
  · filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet] with p hp s hs
    exact (hC (s, p) ⟨⟨hs.1.le, hs.2.le⟩, hp⟩).trans (le_max_left C 0)
  · filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet] with p hp s hs
    exact hdiff s (hsmall ⟨hs.1.le, hs.2.le⟩) p hp

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64AnnulusEnergy_hasDerivAt_of_smooth_variation
    (g : RiemannianMetric n M) (v : ℝ × LoopPlane → M)
    (hv : ContMDiff 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v) (t : ℝ) :
    let E := fun q : ℝ × LoopPlane =>
      m60EnergyDensity g (fun p => v (q.1, p)) q.2
    IntegrableOn (fun p => fderiv ℝ E (t, p) (1, 0)) m64AnnulusDomain volume ∧
      HasDerivAt (fun s => ∫ p in m64AnnulusDomain, E (s, p))
        (∫ p in m64AnnulusDomain, fderiv ℝ E (t, p) (1, 0)) t := by
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun p => v (q.1, p)) q.2
  have hE : ContDiff ℝ ∞ E := contDiff_iff_contDiffAt.mpr fun q =>
    m60EnergyDensity_family_contDiffAt g (hv q)
  change IntegrableOn (fun p => fderiv ℝ E (t, p) (1, 0)) m64AnnulusDomain volume ∧
    HasDerivAt (fun s => ∫ p in m64AnnulusDomain, E (s, p))
      (∫ p in m64AnnulusDomain, fderiv ℝ E (t, p) (1, 0)) t
  refine m64AnnulusIntegral_hasDerivAt_of_continuous_derivative
    (F := fun s p => E (s, p)) (F' := fun s p => fderiv ℝ E (s, p) (1, 0))
    (fun s => hE.continuous.comp (continuous_const.prodMk continuous_id))
    ((hE.continuous_fderiv (by simp)).clm_apply continuous_const) ?_ t
  intro s p
  exact (hE.differentiable (by simp) (s, p)).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s p))

theorem m64AnnulusEnergy_hasDerivAt_of_local_smooth_variation
    (g : RiemannianMetric n M) {v : ℝ × LoopPlane → M}
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {O : Set LoopPlane}
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ O)) :
    let E := fun q : ℝ × LoopPlane =>
      m60EnergyDensity g (fun p => v (q.1, p)) q.2
    IntegrableOn (fun p => fderiv ℝ E (0, p) (1, 0)) m64AnnulusDomain volume ∧
      HasDerivAt (fun s => ∫ p in m64AnnulusDomain, E (s, p))
        (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) 0 := by
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun p => v (q.1, p)) q.2
  have hopen : IsOpen (Ioo (-epsilon) epsilon ×ˢ O) := isOpen_Ioo.prod hO
  have hE : ContDiffOn ℝ ∞ E (Ioo (-epsilon) epsilon ×ˢ O) := by
    intro q hq
    exact (m60EnergyDensity_family_contDiffAt g
      (hv.contMDiffAt (hopen.mem_nhds hq))).contDiffWithinAt
  change IntegrableOn (fun p => fderiv ℝ E (0, p) (1, 0)) m64AnnulusDomain volume ∧
    HasDerivAt (fun s => ∫ p in m64AnnulusDomain, E (s, p))
      (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) 0
  refine m64AnnulusIntegral_hasDerivAt_of_local_continuous_derivative
    (F := fun s p => E (s, p)) (F' := fun s p => fderiv ℝ E (s, p) (1, 0))
    hepsilon ?_ ?_ ?_
  · intro s hs
    exact hE.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp => ⟨hs, hdom hp⟩)
  · have hd := ((hE.fderiv_of_isOpen hopen (m := ∞) (by simp)).clm_apply
      (contDiffOn_const (c := (1, (0 : LoopPlane))))).continuousOn
    exact hd.mono (prod_mono_right hdom)
  · intro s hs p hp
    exact ((hE.contDiffAt (hopen.mem_nhds ⟨hs, hdom hp⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt (l := E) (f := fun s : ℝ => (s, p)) s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s p))

theorem m64AnnulusArea_forward_majorant_of_conformal_smooth_variation
    (g : RiemannianMetric n M) (v : ℝ × LoopPlane → M)
    (hv : ContMDiff 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g (fun z => v (0, z)) p 0 0 =
        m60AreaGram g (fun z => v (0, z)) p 1 1 ∧
      m60AreaGram g (fun z => v (0, z)) p 0 1 = 0) :
    let E := fun q : ℝ × LoopPlane =>
      m60EnergyDensity g (fun p => v (q.1, p)) q.2
    let d := ∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      m64AnnulusArea g (fun p => v (h, p)) ≤
        m64AnnulusArea g (fun p => v (0, p)) + h * (d + eta) := by
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun p => v (q.1, p)) q.2
  let energy := fun s => ∫ p in m64AnnulusDomain, E (s, p)
  let d := ∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)
  have hE : ContDiff ℝ ∞ E := contDiff_iff_contDiffAt.mpr fun q =>
    m60EnergyDensity_family_contDiffAt g (hv q)
  have hint (s : ℝ) : IntegrableOn (fun p => E (s, p)) m64AnnulusDomain volume :=
    (hE.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      |>.integrableOn_compact m64AnnulusDomain_isCompact
  have hcenter : m64AnnulusArea g (fun p => v (0, p)) = energy 0 := by
    apply integral_congr_ae
    filter_upwards [hconformal] with p hp
    exact m60AreaDensity_eq_energyDensity_of_gram g (fun p => v (0, p)) p hp.1 hp.2
  have hupper (s : ℝ) : m64AnnulusArea g (fun p => v (s, p)) ≤ energy s :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun p => m60AreaDensity_nonneg g (fun p => v (s, p)) p)
      (hint s)
      (Eventually.of_forall fun p => m60AreaDensity_le_energyDensity g (fun p => v (s, p)) p)
  have hderiv : HasDerivAt energy d 0 :=
    (m64AnnulusEnergy_hasDerivAt_of_smooth_variation g v hv 0).2
  have hquot : Tendsto (fun h => (energy h - energy 0) / h) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add, smul_eq_mul, ← div_eq_inv_mul] using
      hderiv.tendsto_slope_zero_right
  change ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
    m64AnnulusArea g (fun p => v (h, p)) ≤
      m64AnnulusArea g (fun p => v (0, p)) + h * (d + eta)
  intro eta heta
  have hev := hquot.eventually (Iio_mem_nhds (lt_add_of_pos_right d heta))
  filter_upwards [hev, self_mem_nhdsWithin] with h hh hpos
  have hdiff := (div_le_iff₀ hpos).mp hh.le
  rw [hcenter]
  exact (hupper h).trans (by linarith)

theorem m64AnnulusArea_forward_majorant_of_conformal_local_variation
    (g : RiemannianMetric n M) {v : ℝ × LoopPlane → M}
    {epsilon : ℝ} (hepsilon : 0 < epsilon) {O : Set LoopPlane}
    (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ O))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram g (fun z => v (0, z)) p 0 0 =
        m60AreaGram g (fun z => v (0, z)) p 1 1 ∧
      m60AreaGram g (fun z => v (0, z)) p 0 1 = 0) :
    let E := fun q : ℝ × LoopPlane =>
      m60EnergyDensity g (fun p => v (q.1, p)) q.2
    let d := ∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      m64AnnulusArea g (fun p => v (h, p)) ≤
        m64AnnulusArea g (fun p => v (0, p)) + h * (d + eta) := by
  let E := fun q : ℝ × LoopPlane => m60EnergyDensity g (fun p => v (q.1, p)) q.2
  let energy := fun s => ∫ p in m64AnnulusDomain, E (s, p)
  let d := ∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hE : ContDiffOn ℝ ∞ E (Ioo (-epsilon) epsilon ×ˢ O) := by
    intro q hq
    exact (m60EnergyDensity_family_contDiffAt g
      (hv.contMDiffAt ((isOpen_Ioo.prod hO).mem_nhds hq))).contDiffWithinAt
  have hint (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      IntegrableOn (fun p => E (s, p)) m64AnnulusDomain volume :=
    (hE.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp => ⟨hs, hdom hp⟩)).integrableOn_compact m64AnnulusDomain_isCompact
  have hcenter : m64AnnulusArea g (fun p => v (0, p)) = energy 0 := by
    apply integral_congr_ae
    filter_upwards [hconformal] with p hp
    exact m60AreaDensity_eq_energyDensity_of_gram g (fun p => v (0, p)) p hp.1 hp.2
  have hupper (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      m64AnnulusArea g (fun p => v (s, p)) ≤ energy s :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun p => m60AreaDensity_nonneg g (fun p => v (s, p)) p)
      (hint s hs)
      (Eventually.of_forall fun p => m60AreaDensity_le_energyDensity g (fun p => v (s, p)) p)
  have hderiv : HasDerivAt energy d 0 :=
    (m64AnnulusEnergy_hasDerivAt_of_local_smooth_variation g hepsilon hO hdom hv).2
  have hquot : Tendsto (fun h => (energy h - energy 0) / h) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add, smul_eq_mul, ← div_eq_inv_mul] using hderiv.tendsto_slope_zero_right
  change ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
    m64AnnulusArea g (fun p => v (h, p)) ≤
      m64AnnulusArea g (fun p => v (0, p)) + h * (d + eta)
  intro eta heta
  have hev := hquot.eventually (Iio_mem_nhds (lt_add_of_pos_right d heta))
  have htime : ∀ᶠ h : ℝ in 𝓝[>] 0, h ∈ Ioo (-epsilon) epsilon :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds hzero)
  filter_upwards [hev, htime, self_mem_nhdsWithin] with h hh htime hpos
  have hdiff := (div_le_iff₀ hpos).mp hh.le
  rw [hcenter]
  exact (hupper h htime).trans (by linarith)

end PoincareConjecture
