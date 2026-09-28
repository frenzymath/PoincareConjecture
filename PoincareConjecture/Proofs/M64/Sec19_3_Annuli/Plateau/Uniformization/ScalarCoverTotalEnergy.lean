import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverIntegration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Band" => Set.prod (Ioo (1 : ℝ) 2) (Ioo (-(1 / 2 : ℝ)) (1 / 2))

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

private theorem density_continuous : Continuous (g.pullbackVolumeDensity id) :=
  continuous_iff_continuousAt.mpr fun x =>
    (g.contDiffAt_pullbackVolumeDensity (f := id) (x := x) contMDiffAt_id
      (by simpa using Function.injective_id)).1.continuousAt

private theorem volume_density : g.volumeMeasure =
    volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity id x)) := by
  have h := g.map_restrict_volumeMeasure_symm (OpenPartialHomeomorph.refl Plane)
    contMDiffOn_id contMDiffOn_id
  simpa using h

theorem scalarAnnulus_metric_integral_cover (F : Plane → ℝ) :
    (∫ x in scalarAnnulus, F x ∂g.volumeMeasure) =
      ∫ z in Band, (2 * Real.pi * z.1) * g.pullbackVolumeDensity id (scalarCoverMap z) *
        F (scalarCoverMap z) := by
  have hnon (x : Plane) : 0 ≤ g.pullbackVolumeDensity id x := Real.sqrt_nonneg _
  rw [volume_density, restrict_withDensity scalarAnnulus_isOpen.measurableSet]
  erw [integral_withDensity_eq_integral_toReal_smul₀
      ((ENNReal.continuous_ofReal.comp (density_continuous (g := g))).aemeasurable)
      (by simp)]
  simp only [Function.comp_def, ENNReal.toReal_ofReal (hnon _), smul_eq_mul]
  rw [scalarAnnulus_integral_cover]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro z _
  dsimp only
  ring

theorem scalarAnnulus_metric_integrable_cover {F : Plane → ℝ}
    (hF : IntegrableOn F scalarAnnulus g.volumeMeasure) :
    IntegrableOn (fun z : Cover =>
      (2 * Real.pi * z.1) * g.pullbackVolumeDensity id (scalarCoverMap z) *
        F (scalarCoverMap z)) Band := by
  have hnon (x : Plane) : 0 ≤ g.pullbackVolumeDensity id x := Real.sqrt_nonneg _
  rw [IntegrableOn, volume_density, restrict_withDensity scalarAnnulus_isOpen.measurableSet]
    at hF
  have h := (integrable_withDensity_iff_integrable_smul₀'
    ((ENNReal.continuous_ofReal.comp (density_continuous (g := g))).aemeasurable)
    (by simp)).mp hF
  have hweighted : IntegrableOn (fun x => g.pullbackVolumeDensity id x * F x)
      scalarAnnulus := by
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (hnon _), smul_eq_mul] using! h
  apply (scalarAnnulus_integrable_cover hweighted).congr_fun ?_
    (measurableSet_Ioo.prod measurableSet_Ioo)
  intro z _
  dsimp only
  ring

theorem scalarCoverJacobian_integral_eq_energy {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus) :
    (∫ z in Band, scalarCoverJacobian D H z) =
      ∫ x in scalarAnnulus, g.inner x (D.gradient H x) (D.gradient H x)
        ∂g.volumeMeasure := by
  rw [scalarAnnulus_metric_integral_cover]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
  intro z hz
  exact scalarCoverJacobian_eq_metric_energy D hHs hz.1

theorem scalarPotential_coverJacobian_finite_pos (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ)) :
    IntegrableOn (scalarCoverJacobian D H) Band ∧
      0 < ∫ z in Band, scalarCoverJacobian D H z := by
  constructor
  · apply (scalarAnnulus_metric_integrable_cover
      (scalarPotential_finite_metric_energy D w hHs hHae)).congr_fun ?_
      (measurableSet_Ioo.prod measurableSet_Ioo)
    intro z hz
    exact (scalarCoverJacobian_eq_metric_energy D hHs hz.1).symm
  · rw [scalarCoverJacobian_integral_eq_energy D hHs]
    exact scalarPotential_metric_energy_pos D w hHs hHae

end PoincareConjecture.M64Uniformization
