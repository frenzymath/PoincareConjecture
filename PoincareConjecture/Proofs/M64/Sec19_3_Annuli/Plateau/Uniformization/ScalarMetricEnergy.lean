import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFiniteEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarEnergyPositive














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)







theorem scalarGradient_energy_bound (H : Plane → ℝ) (x : Plane) :
    |g.inner x (D.gradient H x) (D.gradient H x)| ≤
      ‖(g.euclideanCoefficients x).inverse‖ * ‖fderiv ℝ H x‖ ^ 2 := by
  have hdf : mvfderiv (𝓡 2) H x = fderiv ℝ H x := by
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  have hgrad : D.gradient H x = (g.euclideanCoefficients x).inverse (fderiv ℝ H x) := by
    unfold LeviCivitaData.gradient
    rw [hdf]
    rfl
  rw [D.inner_gradient, hdf, hgrad]
  calc
    |fderiv ℝ H x ((g.euclideanCoefficients x).inverse (fderiv ℝ H x))| ≤
        ‖fderiv ℝ H x‖ * ‖(g.euclideanCoefficients x).inverse (fderiv ℝ H x)‖ :=
      (fderiv ℝ H x).le_opNorm _
    _ ≤ ‖fderiv ℝ H x‖ *
        (‖(g.euclideanCoefficients x).inverse‖ * ‖fderiv ℝ H x‖) :=
      mul_le_mul_of_nonneg_left ((g.euclideanCoefficients x).inverse.le_opNorm _)
        (norm_nonneg _)
    _ = _ := by ring






theorem scalarGradient_energy_nonneg (H : Plane → ℝ) (x : Plane) :
    0 ≤ g.inner x (D.gradient H x) (D.gradient H x) := by
  by_cases h : D.gradient H x = 0
  · simp [h]
  · exact (g.pos x _ h).le






theorem scalarGradient_energy_continuousOn {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus) :
    ContinuousOn (fun x => g.inner x (D.gradient H x) (D.gradient H x)) scalarAnnulus := by
  intro x hx
  obtain ⟨V, hVs, -, -, hVH⟩ := exists_compact_smooth_germ scalarAnnulus_isOpen hHs hx
  have heq : (fun y => g.inner y (D.gradient V y) (D.gradient V y)) =ᶠ[𝓝 x]
      (fun y => g.inner y (D.gradient H y) (D.gradient H y)) := by
    filter_upwards [hVH.eventually_nhds] with y hy
    simp only [LeviCivitaData.gradient, Poincare.mvfderiv_eq_of_eventuallyEq hy]
  exact ((D.continuous_inner_gradient hVs hVs).continuousAt.congr_of_eventuallyEq
    heq.symm).continuousWithinAt







theorem scalarPotential_finite_metric_energy (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ)) :
    IntegrableOn (fun x => g.inner x (D.gradient H x) (D.gradient H x))
      scalarAnnulus g.volumeMeasure := by
  let rho : Plane → ℝ := g.pullbackVolumeDensity id
  have hrho : Continuous rho := continuous_iff_continuousAt.mpr fun x =>
    (g.contDiffAt_pullbackVolumeDensity (f := id) (x := x) contMDiffAt_id
      (by simpa using Function.injective_id)).1.continuousAt
  have hrhop (x : Plane) : 0 ≤ rho x := Real.sqrt_nonneg _
  have hIc : Continuous (fun x : Plane => (g.euclideanCoefficients x).inverse) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hi : (g.euclideanCoefficients x).IsInvertible := by
      convert! g.inner_isInvertible x
    exact (hi.contDiffAt_map_inverse.comp x (g.contDiffAt_euclideanCoefficients x)).continuousAt
  let B : Plane → ℝ := fun x => |rho x| * ‖(g.euclideanCoefficients x).inverse‖
  have hBc : Continuous B := by
    dsimp only [B]
    have hn : Continuous (fun A : (Plane →L[ℝ] ℝ) →L[ℝ] Plane => ‖A‖) := by
      convert! (continuous_norm (E := (Plane →L[ℝ] ℝ) →L[ℝ] Plane)) using 1
    exact hrho.abs.mul (hn.comp hIc)
  obtain ⟨p, hp, hmax⟩ := scalarClosedAnnulus_isCompact.exists_isMaxOn
    scalarClosedAnnulus_isConnected.nonempty hBc.continuousOn
  have hEc := scalarGradient_energy_continuousOn D hHs
  have hweighted : IntegrableOn
      (fun x => rho x * g.inner x (D.gradient H x) (D.gradient H x)) scalarAnnulus := by
    apply ((scalarPotential_finite_differential_energy D w hHs hHae).const_mul (B p)).mono'
      ((hrho.continuousOn.mul hEc).aestronglyMeasurable scalarAnnulus_isOpen.measurableSet)
    filter_upwards [ae_restrict_mem scalarAnnulus_isOpen.measurableSet] with x hx
    have hB : B x ≤ B p := hmax (((scalarAnnulusDefining_pos x).mpr hx).le)
    calc
      ‖rho x * g.inner x (D.gradient H x) (D.gradient H x)‖ =
          |rho x| * |g.inner x (D.gradient H x) (D.gradient H x)| := by
        rw [Real.norm_eq_abs, abs_mul]
      _ ≤ |rho x| * (‖(g.euclideanCoefficients x).inverse‖ * ‖fderiv ℝ H x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (scalarGradient_energy_bound D H x) (abs_nonneg _)
      _ = B x * ‖fderiv ℝ H x‖ ^ 2 := by dsimp [B]; ring
      _ ≤ B p * ‖fderiv ℝ H x‖ ^ 2 := mul_le_mul_of_nonneg_right hB (sq_nonneg _)
  have hmu : g.volumeMeasure = volume.withDensity (fun x => ENNReal.ofReal (rho x)) := by
    have h := g.map_restrict_volumeMeasure_symm (OpenPartialHomeomorph.refl Plane)
      contMDiffOn_id contMDiffOn_id
    simpa [rho] using h
  rw [IntegrableOn, hmu, restrict_withDensity scalarAnnulus_isOpen.measurableSet]
  apply (integrable_withDensity_iff_integrable_smul₀'
    ((ENNReal.continuous_ofReal.comp hrho).aemeasurable) (by simp)).mpr
  simpa only [IntegrableOn, Function.comp_def, ENNReal.toReal_ofReal (hrhop _), smul_eq_mul]
    using! hweighted







theorem scalarPotential_metric_energy_pos (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ)) :
    0 < ∫ x in scalarAnnulus, g.inner x (D.gradient H x) (D.gradient H x)
      ∂g.volumeMeasure := by
  have hnon : ¬ ∃ c : ℝ, EqOn H (fun _ => c) scalarAnnulus := by
    rintro ⟨c, hc⟩
    apply scalarPotential_not_ae_constant D w c
    apply hHae.symm.trans
    filter_upwards [ae_restrict_mem scalarAnnulus_isOpen.measurableSet] with x hx
    exact hc hx
  obtain ⟨x, hx, hgrad⟩ := exists_nonzero_annular_gradient D hHs hnon
  let E : Plane → ℝ := fun y => g.inner y (D.gradient H y) (D.gradient H y)
  let U := scalarAnnulus ∩ E ⁻¹' Ioi 0
  have hEc := scalarGradient_energy_continuousOn D hHs
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    exact inter_mem (scalarAnnulus_isOpen.mem_nhds hy.1)
      ((hEc.continuousAt (scalarAnnulus_isOpen.mem_nhds hy.1)).preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hy.2))
  have hUsub : U ⊆ Function.support E ∩ scalarAnnulus := by
    intro y hy
    exact ⟨ne_of_gt hy.2, hy.1⟩
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (scalarGradient_energy_nonneg D H))
    (scalarPotential_finite_metric_energy D w hHs hHae)).mpr
  exact (hU.measure_pos g.volumeMeasure ⟨x, hx, g.pos x _ hgrad⟩).trans_le
    (measure_mono hUsub)

end PoincareConjecture.M64Uniformization
