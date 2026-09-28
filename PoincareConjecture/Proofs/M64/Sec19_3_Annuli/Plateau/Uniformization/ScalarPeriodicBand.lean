import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverTotalEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Cover" => ℝ × ℝ

private theorem periodic_integral_Ioo {f : ℝ → ℝ} (hf : Function.Periodic f 1)
    (a b : ℝ) :
    (∫ t in Ioo a (a + 1), f t) = ∫ t in Ioo b (b + 1), f t := by
  have h := hf.intervalIntegral_add_eq a b
  simpa only [intervalIntegral.integral_of_le (show a ≤ a + 1 by linarith),
    intervalIntegral.integral_of_le (show b ≤ b + 1 by linarith),
    integral_Ioc_eq_integral_Ioo] using h

theorem scalar_periodic_band_transfer {Q : Cover → ℝ}
    (hQc : ContinuousOn Q scalarCoverStrip)
    (hper : ∀ r : ℝ, Function.Periodic (fun t => Q (r, t)) 1)
    (a b : ℝ) (hI : IntegrableOn Q (Ioo (1 : ℝ) 2 ×ˢ Ioo a (a + 1))) :
    IntegrableOn Q (Ioo (1 : ℝ) 2 ×ˢ Ioo b (b + 1)) ∧
      (∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo a (a + 1), Q z) =
        ∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo b (b + 1), Q z := by
  have ha : Integrable Q
      ((volume.restrict (Ioo (1 : ℝ) 2)).prod (volume.restrict (Ioo a (a + 1)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hI
  have hms : AEStronglyMeasurable Q
      ((volume.restrict (Ioo (1 : ℝ) 2)).prod (volume.restrict (Ioo b (b + 1)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hQc.mono (fun _ hz => hz.1)).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioo)
  have hb : Integrable Q
      ((volume.restrict (Ioo (1 : ℝ) 2)).prod (volume.restrict (Ioo b (b + 1)))) := by
    apply (integrable_prod_iff hms).mpr
    constructor
    · filter_upwards [ha.prod_right_ae] with r hr
      have hi : IntervalIntegrable (fun t => Q (r, t)) volume a (a + 1) :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mpr hr
      exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mp
        ((hper r).intervalIntegrable (by norm_num) hi b (b + 1))
    · apply ha.integral_norm_prod_left.congr
      exact ae_of_all _ (fun r => periodic_integral_Ioo
        (show Function.Periodic (fun t => ‖Q (r, t)‖) 1 from
          fun t => congrArg norm (hper r t)) a b)
  constructor
  · rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hb
    exact hb
  · rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← Measure.prod_restrict, integral_prod Q ha, integral_prod Q hb]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r _
    exact periodic_integral_Ioo (hper r) a b

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarPotential_unitCover_energy (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ)) :
    IntegrableOn (scalarCoverJacobian D H) (Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1) ∧
      (∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1, scalarCoverJacobian D H z) =
        (∫ x in scalarAnnulus, g.inner x (D.gradient H x) (D.gradient H x)
          ∂g.volumeMeasure) ∧
      0 < ∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1, scalarCoverJacobian D H z := by
  let E : Plane → ℝ := fun x => g.inner x (D.gradient H x) (D.gradient H x)
  let rho := g.pullbackVolumeDensity id
  let Q : Cover → ℝ := fun z => (2 * Real.pi * z.1) * rho (scalarCoverMap z) *
    E (scalarCoverMap z)
  have hrhoc : Continuous rho := continuous_iff_continuousAt.mpr fun x =>
    (g.contDiffAt_pullbackVolumeDensity (f := id) (x := x) contMDiffAt_id
      (by simpa using Function.injective_id)).1.continuousAt
  have hQc : ContinuousOn Q scalarCoverStrip :=
    (((continuous_const.mul continuous_fst).mul
      (hrhoc.comp scalarCoverMap_smooth.continuous)).continuousOn).mul
      ((scalarGradient_energy_continuousOn D hHs).comp
        scalarCoverMap_smooth.continuous.continuousOn (fun _ hz => scalarCoverMap_mem hz))
  have hper (r : ℝ) : Function.Periodic (fun t => Q (r, t)) 1 := by
    intro t
    have hp := scalarCoverMap_periodic (r, t)
    simp only [Prod.mk_add_mk, add_zero] at hp
    dsimp only [Q]
    rw [hp]
  have hI : IntegrableOn Q
      (Ioo (1 : ℝ) 2 ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    scalarAnnulus_metric_integrable_cover (scalarPotential_finite_metric_energy D w hHs hHae)
  obtain ⟨hunit, hshift⟩ := scalar_periodic_band_transfer hQc hper (-(1 / 2 : ℝ)) 0 (by
    convert! hI using 1
    norm_num)
  norm_num only [neg_add_cancel, zero_add] at hunit hshift
  have hunit' : IntegrableOn Q (Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1) := hunit
  have hshift' : (∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2), Q z) =
      ∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1, Q z := hshift
  have hJQ (z : Cover) (hz : z ∈ scalarCoverStrip) : scalarCoverJacobian D H z = Q z :=
    scalarCoverJacobian_eq_metric_energy D hHs hz
  have henergy : (∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1, scalarCoverJacobian D H z) =
      ∫ x in scalarAnnulus, E x ∂g.volumeMeasure := by
    calc
      _ = ∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1, Q z := by
        apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
        exact fun z hz => hJQ z hz.1
      _ = ∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2), Q z := hshift'.symm
      _ = _ := (scalarAnnulus_metric_integral_cover (g := g) E).symm
  refine ⟨?_, henergy, ?_⟩
  · apply hunit'.congr_fun ?_ (measurableSet_Ioo.prod measurableSet_Ioo)
    exact fun z hz => (hJQ z hz.1).symm
  · rw [henergy]
    exact scalarPotential_metric_energy_pos D w hHs hHae

end PoincareConjecture.M64Uniformization
