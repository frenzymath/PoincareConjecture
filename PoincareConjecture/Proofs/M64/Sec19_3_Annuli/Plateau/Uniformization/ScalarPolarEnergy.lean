import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPolarIntegration
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarTraceEnergy













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open Proofs.M58

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Band" => Set.prod (Ioo (1 : ℝ) 2) (Ioo (-Real.pi) Real.pi)

private theorem polar_mem_annulus {p : ℝ × ℝ} (hp : p.1 ∈ Ioo (1 : ℝ) 2) :
    p.1 • angularPoint p.2 ∈ scalarAnnulus := by
  have hnorm : ‖p.1 • angularPoint p.2‖ = p.1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hp.1),
      norm_angularPoint, mul_one]
  simpa only [scalarAnnulus, mem_ofPred_eq, hnorm, mem_Ioo] using hp







theorem scalarPolar_radial_continuousOn {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus) :
    ContinuousOn (fun p : ℝ × ℝ =>
      fderiv ℝ H (p.1 • angularPoint p.2) (angularPoint p.2)) Band := by
  have hdf : ContinuousOn (fderiv ℝ H) scalarAnnulus :=
    (contMDiffOn_iff_contDiffOn.mp hHs).continuousOn_fderiv_of_isOpen
      scalarAnnulus_isOpen (by simp)
  have hp : Continuous (fun p : ℝ × ℝ => p.1 • angularPoint p.2) :=
    continuous_fst.smul (contDiff_angularPoint.continuous.comp continuous_snd)
  exact (hdf.comp hp.continuousOn (fun p hp => polar_mem_annulus hp.1)).clm_apply
    (contDiff_angularPoint.continuous.comp continuous_snd).continuousOn







theorem scalarPolar_radial_energy_integrable {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus) :
    IntegrableOn (fun p : ℝ × ℝ =>
      (fderiv ℝ H (p.1 • angularPoint p.2) (angularPoint p.2)) ^ 2) Band := by
  have hpolar := scalarAnnulus_integrable_polar hE
  apply hpolar.mono_nonneg
    (((scalarPolar_radial_continuousOn hHs).pow 2).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioo)) (ae_of_all _ (fun _ => sq_nonneg _))
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  have hnorm := (fderiv ℝ H (p.1 • angularPoint p.2)).le_opNorm (angularPoint p.2)
  rw [norm_angularPoint, mul_one, Real.norm_eq_abs] at hnorm
  have hsquare : (fderiv ℝ H (p.1 • angularPoint p.2) (angularPoint p.2)) ^ 2 ≤
      ‖fderiv ℝ H (p.1 • angularPoint p.2)‖ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hnorm
  exact hsquare.trans (le_mul_of_one_le_left (sq_nonneg _) hp.1.1.le)







theorem scalarPolar_radial_memLp_ae {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus) :
    ∀ᵐ theta ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      MemLp (fun r : ℝ => fderiv ℝ H (r • angularPoint theta) (angularPoint theta)) 2
        (volume.restrict (Ioc (1 : ℝ) 2)) := by
  have hi := scalarPolar_radial_energy_integrable hHs hE
  rw [IntegrableOn, Measure.volume_eq_prod] at hi
  erw [← Measure.prod_restrict] at hi
  filter_upwards [hi.prod_left_ae,
    ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (-Real.pi) Real.pi))]
    with theta htheta htheta_mem
  have hc : ContinuousOn (fun r : ℝ =>
      fderiv ℝ H (r • angularPoint theta) (angularPoint theta)) (Ioo (1 : ℝ) 2) :=
    (scalarPolar_radial_continuousOn hHs).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, htheta_mem⟩)
  have hLp := (memLp_two_iff_integrable_sq
    (hc.aestronglyMeasurable measurableSet_Ioo)).mpr htheta
  rwa [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)))]







theorem scalarPolar_radial_hasDerivAt {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) (theta : ℝ) :
    HasDerivAt (fun s : ℝ => H (s • angularPoint theta))
      (fderiv ℝ H (r • angularPoint theta) (angularPoint theta)) r := by
  have hx : r • angularPoint theta ∈ scalarAnnulus :=
    polar_mem_annulus (p := (r, theta)) hr
  have hdx := ((contMDiffOn_iff_contDiffOn.mp hHs).contDiffAt
    (scalarAnnulus_isOpen.mem_nhds hx)).differentiableAt (by simp)
  have h := hdx.hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_id r).smul_const (angularPoint theta))
  simpa only [Function.comp_def, one_smul, id_eq] using! h








theorem scalarPolar_boundary_trace_energy_ae {H : Plane → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    ∀ᵐ theta ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      ∀ r ∈ Ioo (1 : ℝ) 2,
        H (r • angularPoint theta) ^ 2 ≤ (r - 1) *
          ∫ s in (1 : ℝ)..r,
            (fderiv ℝ H (s • angularPoint theta) (angularPoint theta)) ^ 2 ∧
        (1 - H (r • angularPoint theta)) ^ 2 ≤ (2 - r) *
          ∫ s in r..(2 : ℝ),
            (fderiv ℝ H (s • angularPoint theta) (angularPoint theta)) ^ 2 := by
  filter_upwards [scalarPolar_radial_memLp_ae hHs hE] with theta hLp
  intro r hr
  have hc : Continuous (fun s : ℝ => H (s • angularPoint theta)) :=
    hHc.comp (continuous_id.smul continuous_const)
  have hzero : H ((1 : ℝ) • angularPoint theta) = 0 := hinner _ (by
    rw [one_smul, norm_angularPoint])
  have hone : H ((2 : ℝ) • angularPoint theta) = 1 := houter _ (by
    rw [norm_smul, norm_angularPoint, mul_one]
    norm_num)
  constructor
  · have hLpin := MemLp.mono_measure
      (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl hr.2.le)) hLp
    have h := scalar_boundary_trace_energy hr.1 hc.continuousOn
      (fun s hs => scalarPolar_radial_hasDerivAt hHs ⟨hs.1, hs.2.trans hr.2⟩ theta)
      hLpin
    simpa only [hzero, sub_zero] using h
  · have hLpout := MemLp.mono_measure
      (Measure.restrict_mono_set volume (Ioc_subset_Ioc hr.1.le le_rfl)) hLp
    have h := scalar_boundary_trace_energy hr.2 hc.continuousOn
      (fun s hs => scalarPolar_radial_hasDerivAt hHs ⟨hr.1.trans hs.1, hs.2⟩ theta)
      hLpout
    simpa only [hone] using h

end PoincareConjecture.M64Uniformization
