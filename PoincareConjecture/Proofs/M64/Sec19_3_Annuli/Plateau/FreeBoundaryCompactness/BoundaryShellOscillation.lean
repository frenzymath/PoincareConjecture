import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.BoundarySemicircleFTC
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LogarithmicEnergyDrop









set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

local notation "S" => interior m64AnnulusDomain



theorem monotone_boundary_oscillation_sq_mono
    (L : LoopPlane → ℝ)
    (hmono : MonotoneOn (fun t => L (annulusPoint t 0)) (Icc (0 : ℝ) curvePeriod))
    {x u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hx : v < x)
    (hP : x + v < curvePeriod) :
    (L (annulusPoint (x + u) 0) - L (annulusPoint (x - u) 0)) ^ 2 ≤
      (L (annulusPoint (x + v) 0) - L (annulusPoint (x - v) 0)) ^ 2 := by
  have hmleft : L (annulusPoint (x - v) 0) ≤ L (annulusPoint (x - u) 0) := by
    apply hmono <;> (try constructor) <;> linarith
  have hmright : L (annulusPoint (x + u) 0) ≤ L (annulusPoint (x + v) 0) := by
    apply hmono <;> (try constructor) <;> linarith
  have hmnonneg : 0 ≤ L (annulusPoint (x + u) 0) - L (annulusPoint (x - u) 0) := by
    apply sub_nonneg.mpr
    apply hmono <;> (try constructor) <;> linarith
  apply (sq_le_sq₀ hmnonneg (by linarith)).mpr
  linarith




theorem boundary_shell_oscillation
    (L : LoopPlane → ℝ) (hLc : Continuous L) (hL : ContDiffOn ℝ 1 L S)
    (hmono : MonotoneOn (fun t => L (annulusPoint t 0)) (Icc (0 : ℝ) curvePeriod))
    {x rho : ℝ} (hrho : 0 < rho) (hx : rho < x)
    (hP : x + rho < curvePeriod) (hr : rho < 1)
    (hF : IntegrableOn (phaseGradientDensity L) (upperBoundaryShell x rho)) :
    (L (annulusPoint (x + rho * Real.exp (-1)) 0) -
      L (annulusPoint (x - rho * Real.exp (-1)) 0)) ^ 2 ≤
        Real.pi * ∫ p in upperBoundaryShell x rho, phaseGradientDensity L p := by
  let D := boundaryAngularDerivative L x rho
  have hmap : MapsTo (boundaryPolarStrip x rho) S S :=
    fun p hp => upperBoundaryShell_subset_interior hx hP hr
      (boundaryPolarStrip_mapsTo_shell x hrho hp)
  have hDf : ContinuousOn (fderiv ℝ L) S :=
    (hL.fderiv_of_isOpen isOpen_interior (m := 0) (by norm_num)).continuousOn
  have hfield : Continuous (fun p : LoopPlane =>
      (rho * Real.exp (-p 1) / 2) • angularVector (p 0 / 2)) := by
    unfold angularVector
    fun_prop
  have hDc : ContinuousOn D S :=
    (hDf.comp (boundaryPolarStrip_contDiff x rho).continuous.continuousOn hmap).clm_apply
      hfield.continuousOn
  obtain ⟨hD2, henergy⟩ := boundaryAngularDerivative_shell_energy L hL hrho hx hP hr hF
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top m64AnnulusDomain_volume_ne_top (measure_mono interior_subset))
  have hDlp : MemLp D 2 (volume.restrict S) :=
    (memLp_two_iff_integrable_sq
      (hDc.aestronglyMeasurable isOpen_interior.measurableSet)).mpr hD2
  have hDi : IntegrableOn D S := hDlp.integrable (by norm_num)
  have hprod := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hDi
  have hprod2 := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable hD2
  have hsopen : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), s ∈ Ioo (0 : ℝ) 1 := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
    exact ae_restrict_mem measurableSet_Ioo
  have hP0 : (0 : ℝ) ≤ curvePeriod := by unfold curvePeriod; positivity
  have hgood : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      s ∈ Ioo (0 : ℝ) 1 ∧
      IntervalIntegrable (fun t => D (annulusPoint t s)) volume 0 curvePeriod ∧
      IntervalIntegrable (fun t => D (annulusPoint t s) ^ 2) volume 0 curvePeriod := by
    filter_upwards [hsopen, hprod.prod_left_ae, hprod2.prod_left_ae] with s hs h1 h2
    exact ⟨hs, (intervalIntegrable_iff_integrableOn_Icc_of_le hP0).mpr h1,
      (intervalIntegrable_iff_integrableOn_Icc_of_le hP0).mpr h2⟩
  obtain ⟨s, -, ⟨hs, h1, h2⟩, hsel⟩ := m64UnitInterval_exists_le_integral_of_ae
    (fun s => ∫ t in Icc (0 : ℝ) curvePeriod, D (annulusPoint t s) ^ 2)
    hprod2.integral_prod_right hgood
  have hsel' : (∫ t in Icc (0 : ℝ) curvePeriod, D (annulusPoint t s) ^ 2) ≤
      (1 / 2 : ℝ) * ∫ p in upperBoundaryShell x rho, phaseGradientDensity L p := by
    exact (hsel.trans_eq
      (m64AnnulusInteriorIntegral_eq_iterated_swap_integrable _ hD2).symm).trans henergy
  have hosc := boundary_semicircle_oscillation L hLc hL hrho hx hP hr hs h1 h2
  have hrsmall : 0 ≤ rho * Real.exp (-1) := by positivity
  have hrle : rho * Real.exp (-1) ≤ rho * Real.exp (-s) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hs.2])) hrho.le
  have hrmax : rho * Real.exp (-s) ≤ rho :=
    mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (by linarith [hs.1]))
  have hmsquare := monotone_boundary_oscillation_sq_mono L hmono hrsmall hrle
    (hrmax.trans_lt hx) (by linarith : x + rho * Real.exp (-s) < curvePeriod)
  have hfinal := hmsquare.trans (hosc.trans (mul_le_mul_of_nonneg_left hsel' hP0))
  exact hfinal.trans_eq (by unfold curvePeriod; ring)

end PoincareConjecture.M64
