import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverRadialEnergy













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

private theorem partial_energy_le_total {q : ℝ → ℝ}
    (hq : IntegrableOn q (Ioo (1 : ℝ) 2)) (hnon : ∀ s, 0 ≤ q s)
    {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) :
    (∫ s in (1 : ℝ)..r, q s) ≤ (∫ s in Ioo (1 : ℝ) 2, q s) ∧
      (∫ s in r..(2 : ℝ), q s) ≤ ∫ s in Ioo (1 : ℝ) 2, q s := by
  have hfull : IntegrableOn q (Ioc (1 : ℝ) 2) := by
    rw [IntegrableOn, ← Measure.restrict_congr_set
      (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)))]
    exact hq
  constructor
  · rw [intervalIntegral.integral_of_le hr.1.le]
    calc
      _ ≤ ∫ s in Ioc (1 : ℝ) 2, q s :=
        setIntegral_mono_set hfull (ae_of_all _ hnon)
          (Ioc_subset_Ioc le_rfl hr.2.le).eventuallyLE
      _ = _ := integral_Ioc_eq_integral_Ioo
  · rw [intervalIntegral.integral_of_le hr.2.le]
    calc
      _ ≤ ∫ s in Ioc (1 : ℝ) 2, q s :=
        setIntegral_mono_set hfull (ae_of_all _ hnon)
          (Ioc_subset_Ioc hr.1.le le_rfl).eventuallyLE
      _ = _ := integral_Ioc_eq_integral_Ioo







theorem scalarCover_integrated_boundary_trace_energy {H : Plane → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) :
    (∫ t in Ioo (0 : ℝ) 1, H (scalarCoverMap (r, t)) ^ 2) ≤ (r - 1) *
      (∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1,
        (fderiv ℝ (H ∘ scalarCoverMap) z (1, 0)) ^ 2) ∧
    (∫ t in Ioo (0 : ℝ) 1, (1 - H (scalarCoverMap (r, t))) ^ 2) ≤ (2 - r) *
      (∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1,
        (fderiv ℝ (H ∘ scalarCoverMap) z (1, 0)) ^ 2) := by
  let q : Cover → ℝ := fun z => (fderiv ℝ (H ∘ scalarCoverMap) z (1, 0)) ^ 2
  have hq := scalarCover_radial_energy_integrable hHs hE
  have hprod : Integrable q
      ((volume.restrict (Ioo (1 : ℝ) 2)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hq
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      H (scalarCoverMap (r, t)) ^ 2 ≤ (r - 1) * (∫ s in Ioo (1 : ℝ) 2, q (s, t)) ∧
      (1 - H (scalarCoverMap (r, t))) ^ 2 ≤
        (2 - r) * (∫ s in Ioo (1 : ℝ) 2, q (s, t)) := by
    filter_upwards [scalarCover_boundary_trace_energy_ae hHc hHs hE hinner houter,
      hprod.prod_left_ae] with t ht hqt
    have hpartial := partial_energy_le_total hqt (fun _ => sq_nonneg _) hr
    exact ⟨(ht r hr).1.trans (mul_le_mul_of_nonneg_left hpartial.1 (sub_pos.mpr hr.1).le),
      (ht r hr).2.trans (mul_le_mul_of_nonneg_left hpartial.2 (sub_pos.mpr hr.2).le)⟩
  have hcircle : Continuous (fun t : ℝ => H (scalarCoverMap (r, t))) :=
    hHc.comp (scalarCoverMap_smooth.continuous.comp (continuous_const.prodMk continuous_id))
  have hin : IntegrableOn (fun t : ℝ => H (scalarCoverMap (r, t)) ^ 2) (Ioo (0 : ℝ) 1) :=
    ((hcircle.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self
  have hout : IntegrableOn (fun t : ℝ => (1 - H (scalarCoverMap (r, t))) ^ 2)
      (Ioo (0 : ℝ) 1) :=
    (((continuous_const.sub hcircle).pow 2).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have htotal : (∫ t in Ioo (0 : ℝ) 1, ∫ s in Ioo (1 : ℝ) 2, q (s, t)) =
      ∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1, q z := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact (integral_prod_symm q hprod).symm
  constructor
  · have h := integral_mono_ae hin (hprod.integral_prod_right.const_mul (r - 1))
      (hpoint.mono (fun _ h => h.1))
    simpa only [integral_const_mul, htotal] using h
  · have h := integral_mono_ae hout (hprod.integral_prod_right.const_mul (2 - r))
      (hpoint.mono (fun _ h => h.2))
    simpa only [integral_const_mul, htotal] using h

end PoincareConjecture.M64Uniformization
