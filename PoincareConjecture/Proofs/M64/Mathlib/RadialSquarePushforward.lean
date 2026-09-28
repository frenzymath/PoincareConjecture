import PoincareConjecture.Proofs.M64.Mathlib.RadialTestVanishing
import Mathlib.Analysis.Real.Sqrt















set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff

namespace PoincareConjecture

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]






theorem exists_squaredRadius_representative {R : ℝ} {C : ℝ → F}
    (hC : IntegrableOn C (Ioo (0 : ℝ) R)) :
    ∃ f : ℝ → F, StronglyMeasurable f ∧
      Integrable f (Measure.map (fun r : ℝ => r ^ 2) (volume.restrict (Ioo 0 R))) ∧
      (∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), f (r ^ 2) = C r) ∧
      ∀ psi : ℝ → ℝ, Continuous psi →
        (∫ t, psi t • f t ∂Measure.map (fun r : ℝ => r ^ 2)
          (volume.restrict (Ioo 0 R))) =
        ∫ r in Ioo (0 : ℝ) R, psi (r ^ 2) • C r := by
  let Cm := hC.aestronglyMeasurable.mk C
  let f := Cm ∘ Real.sqrt
  have hCm : StronglyMeasurable Cm := hC.aestronglyMeasurable.stronglyMeasurable_mk
  have hf : StronglyMeasurable f := hCm.comp_measurable Real.continuous_sqrt.measurable
  have hsq : Measurable (fun r : ℝ => r ^ 2) := measurable_id.pow_const 2
  have heq : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R), f (r ^ 2) = C r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      hC.aestronglyMeasurable.ae_eq_mk] with r hr hCr
    simpa only [f, Function.comp_apply, Real.sqrt_sq hr.1.le] using hCr.symm
  have hfi : Integrable f
      (Measure.map (fun r : ℝ => r ^ 2) (volume.restrict (Ioo 0 R))) :=
    (integrable_map_measure hf.aestronglyMeasurable hsq.aemeasurable).mpr
      (hC.congr (heq.mono fun _ hr => hr.symm))
  refine ⟨f, hf, hfi, heq, ?_⟩
  intro psi hpsi
  have htest : StronglyMeasurable (fun t => psi t • f t) :=
    hpsi.stronglyMeasurable.smul hf
  calc
    _ = ∫ r in Ioo (0 : ℝ) R, psi (r ^ 2) • f (r ^ 2) :=
      integral_map_of_stronglyMeasurable
        (μ := volume.restrict (Ioo (0 : ℝ) R)) hsq htest
    _ = _ := integral_congr_ae
      (heq.mono fun r hr => congrArg (fun z => psi (r ^ 2) • z) hr)

variable [CompleteSpace F]






theorem radialCoefficient_ae_eq_zero_of_sq_test_pairings
    {a b R : ℝ} {C : ℝ → F}
    (hC : IntegrableOn C (Ioo (0 : ℝ) R))
    (hpair : ∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Ioo (a ^ 2) (b ^ 2) →
      (∫ r in Ioo (0 : ℝ) R, psi (r ^ 2) • C r) = 0) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      r ^ 2 ∈ Ioo (a ^ 2) (b ^ 2) → C r = 0 := by
  obtain ⟨f, _, hfi, heq, htransport⟩ := exists_squaredRadius_representative hC
  have hzero := radialCoefficient_ae_eq_zero_of_test_pairings
    (hfi.locallyIntegrable.locallyIntegrableOn (Ioo (a ^ 2) (b ^ 2)))
    (fun psi hp hc hs => (htransport psi hp.continuous).trans (hpair psi hp hc hs))
  have hpull := ae_of_ae_map (measurable_id.pow_const 2).aemeasurable
    ((ae_restrict_iff' measurableSet_Ioo).mp hzero)
  filter_upwards [heq, hpull] with r hr hz
  intro hrsq
  exact hr.symm.trans (hz hrsq)






theorem radialWeightedCoefficients_ae_zero_of_sq_test_pairings
    {a b R : ℝ} {D0 D1 : ℝ → F}
    (h0 : IntegrableOn (fun r => r • D0 r) (Ioo (0 : ℝ) R))
    (h1 : IntegrableOn (fun r => r ^ 2 • D1 r) (Ioo (0 : ℝ) R))
    (hpair : ∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Ioo (a ^ 2) (b ^ 2) →
      (∫ r in Ioo (0 : ℝ) R, (r * psi (r ^ 2)) • D0 r) = 0 ∧
      (∫ r in Ioo (0 : ℝ) R, (r ^ 2 * psi (r ^ 2)) • D1 r) = 0) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      r ^ 2 ∈ Ioo (a ^ 2) (b ^ 2) → D0 r = 0 ∧ D1 r = 0 := by
  have hz0 := radialCoefficient_ae_eq_zero_of_sq_test_pairings h0
    (fun psi hp hc hs => by
      simpa only [smul_smul, mul_comm] using (hpair psi hp hc hs).1)
  have hz1 := radialCoefficient_ae_eq_zero_of_sq_test_pairings h1
    (fun psi hp hc hs => by
      simpa only [smul_smul, mul_comm] using (hpair psi hp hc hs).2)
  filter_upwards [hz0, hz1, ae_restrict_mem measurableSet_Ioo] with r hzero0 hzero1 hr
  intro hrsq
  exact ⟨(smul_eq_zero.mp (hzero0 hrsq)).resolve_left hr.1.ne',
    (smul_eq_zero.mp (hzero1 hrsq)).resolve_left (pow_ne_zero 2 hr.1.ne')⟩






theorem radialWeightedCoefficients_common_radius
    {a b R : ℝ} {D0 D1 : ℝ → F} (ha : 0 ≤ a) (hab : a < b) (hbR : b ≤ R)
    (h0 : IntegrableOn (fun r => r • D0 r) (Ioo (0 : ℝ) R))
    (h1 : IntegrableOn (fun r => r ^ 2 • D1 r) (Ioo (0 : ℝ) R))
    (hpair : ∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Ioo (a ^ 2) (b ^ 2) →
      (∫ r in Ioo (0 : ℝ) R, (r * psi (r ^ 2)) • D0 r) = 0 ∧
      (∫ r in Ioo (0 : ℝ) R, (r ^ 2 * psi (r ^ 2)) • D1 r) = 0) :
    (∀ᵐ r ∂volume.restrict (Ioo a b), D0 r = 0 ∧ D1 r = 0) ∧
      ∃ r ∈ Ioo a b, D0 r = 0 ∧ D1 r = 0 := by
  have hz := radialWeightedCoefficients_ae_zero_of_sq_test_pairings h0 h1 hpair
  have hsub : Ioo a b ⊆ Ioo (0 : ℝ) R :=
    fun r hr => ⟨ha.trans_lt hr.1, hr.2.trans_le hbR⟩
  have hboth : ∀ᵐ r ∂volume.restrict (Ioo a b), D0 r = 0 ∧ D1 r = 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hz,
      ae_restrict_mem measurableSet_Ioo] with r hr hrab
    apply hr
    exact ⟨(sq_lt_sq₀ ha (ha.trans hrab.1.le)).mpr hrab.1,
      (sq_lt_sq₀ (ha.trans hrab.1.le) (ha.trans hab.le)).mpr hrab.2⟩
  exact exists_common_good_radius_of_ae hab (hboth.mono fun r hr => hr.1)
    (hboth.mono fun r hr => hr.2)

end PoincareConjecture
