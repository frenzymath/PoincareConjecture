import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBandExhaustion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarCoverJacobian_integral_eq_period {H : Plane → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus)
    (hJ : IntegrableOn (scalarCoverJacobian D H)
      (Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1))
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    (∫ z in Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1, scalarCoverJacobian D H z) =
      scalarFluxPeriod D H (3 / 2) := by
  let epsilon : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 1)) / 4
  have hepsilon (n : ℕ) : 0 < epsilon n := by dsimp only [epsilon]; positivity
  have hepsilon_le (n : ℕ) : epsilon n ≤ 1 / 4 := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hepsilon_lim : Tendsto epsilon atTop (𝓝 0) := by
    simpa only [epsilon, zero_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 4
  have hchoices (n : ℕ) : ∃ a ∈ Ioo (1 : ℝ) 2,
      a - 1 < epsilon n ∧ |scalarCoverWeightedFlux D H a| < epsilon n ∧
      ∃ b ∈ Ioo (1 : ℝ) 2, 2 - b < epsilon n ∧
        |scalarFluxPeriod D H b - scalarCoverWeightedFlux D H b| < epsilon n := by
    obtain ⟨⟨a, ha, haNear, haFlux⟩, ⟨b, hb, hbNear, hbFlux⟩⟩ :=
      scalarCover_exists_boundary_flux_approximation D hHc hHs hlap hE hinner houter
        (hepsilon n) (hepsilon n)
    exact ⟨a, ha, haNear, haFlux, b, hb, hbNear, hbFlux⟩
  choose a ha haNear haFlux b hb hbNear hbFlux using hchoices
  have halim : Tendsto a atTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hepsilon_lim
    simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (ha n).1)] using (haNear n).le
  have hblim : Tendsto b atTop (𝓝 2) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hepsilon_lim
    have h := (hbNear n).le
    simpa only [Real.norm_eq_abs, abs_of_neg (sub_neg.mpr (hb n).2), neg_sub] using h
  have hab (n : ℕ) : a n ≤ b n := by
    have haN := haNear n
    have hbN := hbNear n
    have hbound := hepsilon_le n
    linarith
  let J := scalarCoverJacobian D H
  let I : ℕ → ℝ := fun n => ∫ z in Icc (a n) (b n) ×ˢ Ioo (0 : ℝ) 1, J z
  have hgreen (n : ℕ) : I n =
      scalarCoverWeightedFlux D H (b n) - scalarCoverWeightedFlux D H (a n) := by
    have hAE : (Icc (a n) (b n) ×ˢ Ioo (0 : ℝ) 1 : Set Cover) =ᵐ[volume]
        Icc (a n, (0 : ℝ)) (b n, 1) := by
      rw [Icc_prod_eq, Measure.volume_eq_prod]
      exact Measure.set_prod_ae_eq EventuallyEq.rfl Ioo_ae_eq_Icc
    change (∫ z in Icc (a n) (b n) ×ˢ Ioo (0 : ℝ) 1, scalarCoverJacobian D H z) = _
    rw [setIntegral_congr_set hAE]
    exact scalarCover_green_identity D hHs hlap (ha n) (hb n) (hab n)
  have hfull := scalar_integral_band_tendsto hJ (fun n => (ha n).1)
    (fun n => (hb n).2) halim hblim
  have hperiod : Tendsto I atTop (𝓝 (scalarFluxPeriod D H (3 / 2))) := by
    apply Metric.tendsto_atTop.mpr
    intro delta hdelta
    have hev : ∀ᶠ n in atTop, epsilon n < delta / 2 :=
      (tendsto_order.mp hepsilon_lim).2 _ (half_pos hdelta)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, hgreen, abs_lt]
    have haF := abs_lt.mp (haFlux n)
    have hbF := hbFlux n
    rw [scalarFluxPeriod_eq D hHs hlap (hb n) (by norm_num : (3 / 2 : ℝ) ∈ Ioo 1 2)]
      at hbF
    have hbF' := abs_lt.mp hbF
    constructor <;> linarith [hN n hn]
  exact tendsto_nhds_unique hfull hperiod

theorem scalarPotential_energy_eq_period (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ))
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    (∫ x in scalarAnnulus, g.inner x (D.gradient H x) (D.gradient H x)
      ∂g.volumeMeasure) = scalarFluxPeriod D H (3 / 2) := by
  obtain ⟨hJ, henergy, -⟩ := scalarPotential_unitCover_energy D w hHs hHae
  rw [← henergy]
  exact scalarCoverJacobian_integral_eq_period D hHc hHs hlap
    (scalarPotential_finite_differential_energy D w hHs hHae) hJ hinner houter

end PoincareConjecture.M64Uniformization
