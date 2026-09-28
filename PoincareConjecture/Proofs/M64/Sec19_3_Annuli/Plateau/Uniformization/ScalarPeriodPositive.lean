import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFluxApproximation














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






theorem scalarCoverJacobian_continuousOn {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0) :
    ContinuousOn (scalarCoverJacobian D H) scalarCoverStrip := by
  have hdu := (scalarCoverPotential_smooth hHs).continuousOn_fderiv_of_isOpen
    scalarCoverStrip_isOpen (by simp)
  have hb := (scalarCoverForm_smooth_closed D hHs hlap).1.continuousOn
  exact ((hdu.clm_apply continuousOn_const).mul (hb.clm_apply continuousOn_const)).sub
    ((hdu.clm_apply continuousOn_const).mul (hb.clm_apply continuousOn_const))







theorem exists_scalarCover_weighted_flux_strict (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ))
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0) :
    ∃ r ∈ Ioo (1 : ℝ) 2, ∃ s ∈ Ioo (1 : ℝ) 2,
      r < s ∧ scalarCoverWeightedFlux D H r < scalarCoverWeightedFlux D H s := by
  let J := scalarCoverJacobian D H
  have hJc := scalarCoverJacobian_continuousOn D hHs hlap
  obtain ⟨hI, -, hpositive⟩ := scalarPotential_unitCover_energy D w hHs hHae
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1)] J := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
    exact scalarCoverJacobian_nonneg D hHs hz.1
  have hsupport := (setIntegral_pos_iff_support_of_nonneg_ae hn hI).mp hpositive
  obtain ⟨z, hzJ, hz⟩ := nonempty_of_measure_ne_zero hsupport.ne'
  have hzpositive : 0 < J z := by
    have hznon := scalarCoverJacobian_nonneg D hHs hz.1
    exact lt_of_le_of_ne hznon (Ne.symm hzJ)
  obtain ⟨r, hr1, hrz⟩ := exists_between hz.1.1
  obtain ⟨s, hzs, hs2⟩ := exists_between hz.1.2
  have hr : r ∈ Ioo (1 : ℝ) 2 := ⟨hr1, hrz.trans hz.1.2⟩
  have hs : s ∈ Ioo (1 : ℝ) 2 := ⟨hz.1.1.trans hzs, hs2⟩
  have hrs : r < s := hrz.trans hzs
  let K := Icc (r, (0 : ℝ)) (s, 1)
  have hK : K ⊆ scalarCoverStrip :=
    fun y hy => ⟨hr1.trans_le hy.1.1, hy.2.1.trans_lt hs2⟩
  let U := (Ioo r s ×ˢ Ioo (0 : ℝ) 1) ∩ J ⁻¹' Ioi 0
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hystrip : y ∈ scalarCoverStrip := ⟨hr1.trans hy.1.1.1, hy.1.1.2.trans hs2⟩
    exact inter_mem ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hy.1)
      ((hJc.continuousAt (scalarCoverStrip_isOpen.mem_nhds hystrip)).preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hy.2))
  have hUsub : U ⊆ Function.support J ∩ K := by
    intro y hy
    exact ⟨ne_of_gt hy.2, ⟨hy.1.1.1.le, hy.1.2.1.le⟩,
      ⟨hy.1.1.2.le, hy.1.2.2.le⟩⟩
  have hJint : IntegrableOn J K := (hJc.mono hK).integrableOn_compact isCompact_Icc
  have hJn : 0 ≤ᵐ[volume.restrict K] J := by
    filter_upwards [ae_restrict_mem (show MeasurableSet K from measurableSet_Icc)] with y hy
    exact scalarCoverJacobian_nonneg D hHs (hK hy)
  have hbandpositive : 0 < ∫ y in K, J y := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hJn hJint).mpr
    exact (hU.measure_pos volume ⟨z, ⟨⟨hrz, hzs⟩, hz.2⟩, hzpositive⟩).trans_le
      (measure_mono hUsub)
  have hgreen := scalarCover_green_identity D hHs hlap hr hs hrs.le
  change (∫ y in K, J y) = _ at hgreen
  rw [hgreen] at hbandpositive
  exact ⟨r, hr, s, hs, hrs, sub_pos.mp hbandpositive⟩







theorem scalarPotential_fluxPeriod_pos (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ))
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) : 0 < scalarFluxPeriod D H r := by
  have hE := scalarPotential_finite_differential_energy D w hHs hHae
  obtain ⟨a, ha, b, hb, -, hstrict⟩ := exists_scalarCover_weighted_flux_strict D w hHs hHae hlap
  have halower := (scalarCover_weighted_flux_bounds D hHc hHs hlap hE hinner houter ha).1
  have hbupper := (scalarCover_weighted_flux_bounds D hHc hHs hlap hE hinner houter hb).2
  rw [scalarFluxPeriod_eq D hHs hlap hb hr] at hbupper
  exact (halower.trans_lt hstrict).trans_le hbupper







theorem exists_positive_period_annular_cover_conjugate :
    ∃ (H : Plane → ℝ) (w : H1Zero D scalarAnnulus) (V : Cover → ℝ),
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
        (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ) ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      (∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) ∧
      0 < scalarFluxPeriod D H (3 / 2) ∧
      ContDiffOn ℝ ∞ V scalarCoverStrip ∧
      (∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z) ∧
      ∀ z ∈ scalarCoverStrip,
        V (z + (0, 1)) = V z + scalarFluxPeriod D H (3 / 2) := by
  obtain ⟨H, w, hHc, hHs, hHae, hlap, hinner, houter, hrange, -, -⟩ :=
    exists_finite_energy_annular_harmonic_potential D
  obtain ⟨V, hVs, hdV, hdeck⟩ := exists_annular_cover_conjugate_with_period D hHs hlap
  exact ⟨H, w, V, hHc, hHs, hHae, hlap, hinner, houter, hrange,
    scalarPotential_fluxPeriod_pos D w hHc hHs hHae hlap hinner houter (by norm_num),
    hVs, hdV, hdeck⟩

end PoincareConjecture.M64Uniformization
