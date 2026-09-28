import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPeriodicBand
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundarySelection













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ







theorem scalarCover_differential_energy_integrable {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus) :
    IntegrableOn (fun z : Cover => ‖fderiv ℝ H (scalarCoverMap z)‖ ^ 2)
      (Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1) := by
  let Q : Cover → ℝ := fun z => (2 * Real.pi * z.1) *
    ‖fderiv ℝ H (scalarCoverMap z)‖ ^ 2
  have hdfc : ContinuousOn (fderiv ℝ H) scalarAnnulus :=
    (contMDiffOn_iff_contDiffOn.mp hHs).continuousOn_fderiv_of_isOpen
      scalarAnnulus_isOpen (by simp)
  have hEc : ContinuousOn (fun z : Cover => ‖fderiv ℝ H (scalarCoverMap z)‖ ^ 2)
      scalarCoverStrip :=
    ((hdfc.comp scalarCoverMap_smooth.continuous.continuousOn
      (fun _ hz => scalarCoverMap_mem hz)).norm).pow 2
  have hQc : ContinuousOn Q scalarCoverStrip :=
    (continuous_const.mul continuous_fst).continuousOn.mul hEc
  have hper (r : ℝ) : Function.Periodic (fun t => Q (r, t)) 1 := by
    intro t
    have hp := scalarCoverMap_periodic (r, t)
    simp only [Prod.mk_add_mk, add_zero] at hp
    dsimp only [Q]
    rw [hp]
  have hI : IntegrableOn Q
      (Ioo (1 : ℝ) 2 ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    scalarAnnulus_integrable_cover hE
  have hunit := (scalar_periodic_band_transfer hQc hper (-(1 / 2 : ℝ)) 0 (by
    convert! hI using 1
    norm_num)).1
  norm_num only [zero_add] at hunit
  apply (hunit.const_mul (1 / (2 * Real.pi))).mono_nonneg
    ((hEc.mono (fun _ hz => hz.1)).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioo)) (ae_of_all _ (fun _ => sq_nonneg _))
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
  calc
    _ ≤ z.1 * ‖fderiv ℝ H (scalarCoverMap z)‖ ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) hz.1.1.le
    _ = (1 / (2 * Real.pi)) * Q z := by
      dsimp only [Q]
      field_simp







theorem scalarCover_circle_energy_integrable {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus) :
    IntegrableOn (fun r : ℝ => ∫ t in Ioo (0 : ℝ) 1,
      ‖fderiv ℝ H (scalarCoverMap (r, t))‖ ^ 2) (Ioo (1 : ℝ) 2) := by
  have hi := scalarCover_differential_energy_integrable hHs hE
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  exact hi.integral_prod_left







theorem scalarCover_exists_small_energy_circles {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon) (hdelta : 0 < delta) :
    (∃ r ∈ Ioo (1 : ℝ) 2, r - 1 < delta ∧
      (r - 1) * (∫ t in Ioo (0 : ℝ) 1,
        ‖fderiv ℝ H (scalarCoverMap (r, t))‖ ^ 2) < epsilon) ∧
    (∃ r ∈ Ioo (1 : ℝ) 2, 2 - r < delta ∧
      (2 - r) * (∫ t in Ioo (0 : ℝ) 1,
        ‖fderiv ℝ H (scalarCoverMap (r, t))‖ ^ 2) < epsilon) := by
  have hi := scalarCover_circle_energy_integrable hHs hE
  have hnon (r : ℝ) (_hr : r ∈ Ioo (1 : ℝ) 2) :
      0 ≤ ∫ t in Ioo (0 : ℝ) 1, ‖fderiv ℝ H (scalarCoverMap (r, t))‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  exact ⟨scalar_exists_inner_small_energy_radius (by norm_num) hi hnon hepsilon hdelta,
    scalar_exists_outer_small_energy_radius (by norm_num) hi hnon hepsilon hdelta⟩

end PoincareConjecture.M64Uniformization
