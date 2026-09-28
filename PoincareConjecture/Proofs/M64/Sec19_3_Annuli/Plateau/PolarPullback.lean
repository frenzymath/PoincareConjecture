import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PolarStrip
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "Q" => m64AnnulusInterior

private theorem box_mem {p : LoopPlane} (hp : p ∈ Q) :
    0 < p 0 ∧ p 0 < curvePeriod ∧ 0 < p 1 ∧ p 1 < 1 := by
  have h0 := hp 0 (mem_univ _)
  have h1 := hp 1 (mem_univ _)
  exact ⟨h0.1, h0.2, h1.1, h1.2⟩

private theorem box_subset : Q ⊆ m64AnnulusDomain := by
  intro p hp
  obtain ⟨h0, hT, h1, h2⟩ := box_mem hp
  exact ⟨h0.le, hT.le, h1.le, h2.le⟩

private theorem box_restrict : volume.restrict Q = volume.restrict S := by
  rw [← m64Annulus_restrict_closed_eq_interior]
  exact Measure.restrict_congr_set m64AnnulusDomain_ae_eq_interior.symm

private theorem polar_inj (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) :
    InjOn (m64MorreyPolarStrip a rho) Q := by
  intro p hp q hq heq
  exact m64MorreyPolarStrip_injOn a hrho
    (show 0 < p 0 ∧ p 0 < curvePeriod from ⟨(box_mem hp).1, (box_mem hp).2.1⟩)
    (show 0 < q 0 ∧ q 0 < curvePeriod from ⟨(box_mem hq).1, (box_mem hq).2.1⟩) heq

theorem m64MorreyPolarStrip_integrable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) {F : LoopPlane → E}
    (hF : IntegrableOn F (Metric.closedBall a rho) volume) :
    IntegrableOn (fun p => F (m64MorreyPolarStrip a rho p)) S volume := by
  let P := m64MorreyPolarStrip a rho
  let J := fun p : LoopPlane => (rho * Real.exp (-p 1)) ^ 2
  let c := (rho * Real.exp (-1)) ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hPQ : P '' Q ⊆ Metric.closedBall a rho :=
    (m64MorreyPolarStrip_mapsTo_closedBall a hrho.le).image_subset.trans'
      (image_mono box_subset)
  have hw := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    isOpen_m64AnnulusInterior.measurableSet
    (fun p _ =>
      ((m64MorreyPolarStrip_contDiff a rho).differentiable (by simp) p)
        |>.hasFDerivAt.hasFDerivWithinAt)
    (polar_inj a hrho) F).mp (hF.mono_set hPQ)
  have hw' : IntegrableOn (fun p => J p • F (P p)) Q volume := by
    simpa only [m64MorreyPolarStrip_det, abs_sq] using hw
  have hJ : Continuous (fun p => (J p)⁻¹) := by
    apply Continuous.inv₀
    · dsimp [J]; fun_prop
    · intro p; dsimp [J]; positivity
  have hb : ∀ᵐ p ∂volume.restrict Q, ‖(J p)⁻¹‖ ≤ c⁻¹ := by
    filter_upwards [ae_restrict_mem isOpen_m64AnnulusInterior.measurableSet] with p hp
    have hj := m64MorreyPolarStrip_jacobian_lower a hrho (box_subset hp)
    rw [m64MorreyPolarStrip_det, abs_of_nonneg (sq_nonneg _)] at hj
    rw [Real.norm_eq_abs, abs_of_pos (by dsimp [J]; positivity)]
    exact inv_anti₀ hc hj
  have hi := hw'.bdd_smul c⁻¹ hJ.aestronglyMeasurable hb
  have heq : (fun p => (J p)⁻¹ • (J p • F (P p))) = (fun p => F (P p)) := by
    funext p
    rw [smul_smul, inv_mul_cancel₀ (by dsimp [J]; positivity), one_smul]
  change IntegrableOn (fun p => (J p)⁻¹ • (J p • F (P p))) Q volume at hi
  rw [heq] at hi
  change Integrable _ (volume.restrict Q) at hi
  rwa [box_restrict] at hi

theorem m64MorreyPolarStrip_integral_le (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho)
    {F : LoopPlane → ℝ} (hF : IntegrableOn F (Metric.closedBall a rho) volume)
    (hpos : ∀ p, 0 ≤ F p) :
    (∫ p in S, F (m64MorreyPolarStrip a rho p)) ≤
      ((rho * Real.exp (-1)) ^ 2)⁻¹ * ∫ p in Metric.closedBall a rho, F p := by
  let P := m64MorreyPolarStrip a rho
  let c := (rho * Real.exp (-1)) ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hPQ : P '' Q ⊆ Metric.closedBall a rho :=
    (m64MorreyPolarStrip_mapsTo_closedBall a hrho.le).image_subset.trans'
      (image_mono box_subset)
  have hw := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    isOpen_m64AnnulusInterior.measurableSet
    (fun p _ =>
      ((m64MorreyPolarStrip_contDiff a rho).differentiable (by simp) p)
        |>.hasFDerivAt.hasFDerivWithinAt)
    (polar_inj a hrho) F).mp (hF.mono_set hPQ)
  have hi : IntegrableOn (fun p => F (P p)) Q volume := by
    change Integrable _ (volume.restrict Q)
    rw [box_restrict]
    exact m64MorreyPolarStrip_integrable a hrho hF
  have hb : c * (∫ p in S, F (P p)) ≤ ∫ p in Metric.closedBall a rho, F p := by
    calc
      _ = ∫ p in Q, c * F (P p) := by rw [integral_const_mul, box_restrict]
      _ ≤ ∫ p in Q, |(fderiv ℝ P p).det| • F (P p) := by
        apply setIntegral_mono_on (hi.const_mul c) hw isOpen_m64AnnulusInterior.measurableSet
        intro p hp
        exact mul_le_mul_of_nonneg_right
          (m64MorreyPolarStrip_jacobian_lower a hrho (box_subset hp)) (hpos _)
      _ = ∫ p in P '' Q, F p :=
        (integral_image_eq_integral_abs_det_fderiv_smul volume
          isOpen_m64AnnulusInterior.measurableSet
          (fun p _ => ((m64MorreyPolarStrip_contDiff a rho).differentiable (by simp) p)
            |>.hasFDerivAt.hasFDerivWithinAt)
          (polar_inj a hrho) F).symm
      _ ≤ _ := setIntegral_mono_set hF (by filter_upwards [] with p; exact hpos p)
        (Filter.Eventually.of_forall hPQ)
  simpa only [div_eq_inv_mul] using (le_div_iff₀' hc).mpr hb

theorem m64MorreyPolarStrip_memLp_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) {u : LoopPlane → E}
    (hu : MemLp u 2 (volume.restrict (Metric.closedBall a rho))) :
    MemLp (fun p => u (m64MorreyPolarStrip a rho p)) 2 (volume.restrict S) := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall a rho)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall a rho).measure_lt_top.ne
  have hi := m64MorreyPolarStrip_integrable a hrho (hu.integrable (by norm_num))
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  exact m64MorreyPolarStrip_integrable a hrho
    ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu)

theorem m64MorreyPolarStrip_strong_square_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (f : ℕ → LoopPlane → E) (u : LoopPlane → E)
    (hi : ∀ j, IntegrableOn (fun p => ‖f j p - u p‖ ^ 2) (Metric.closedBall a rho) volume)
    (hlim : Tendsto (fun j => ∫ p in Metric.closedBall a rho, ‖f j p - u p‖ ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun j => ∫ p in S,
      ‖f j (m64MorreyPolarStrip a rho p) - u (m64MorreyPolarStrip a rho p)‖ ^ 2)
      atTop (𝓝 0) := by
  have hupper := hlim.const_mul (((rho * Real.exp (-1)) ^ 2)⁻¹)
  simp only [mul_zero] at hupper
  apply squeeze_zero (fun j => integral_nonneg (fun p => sq_nonneg _))
    (fun j => m64MorreyPolarStrip_integral_le a hrho (hi j) (fun p => sq_nonneg _)) hupper

theorem m64MorreyPolarStrip_weighted_integrable
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) {F : LoopPlane → ℝ}
    (hF : IntegrableOn F (Metric.closedBall a rho) volume) :
    IntegrableOn (fun p => (rho * Real.exp (-p 1)) ^ 2 *
      F (m64MorreyPolarStrip a rho p)) S volume := by
  have hPQ : m64MorreyPolarStrip a rho '' Q ⊆ Metric.closedBall a rho :=
    (m64MorreyPolarStrip_mapsTo_closedBall a hrho.le).image_subset.trans'
      (image_mono box_subset)
  have hw := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    isOpen_m64AnnulusInterior.measurableSet
    (fun p _ => ((m64MorreyPolarStrip_contDiff a rho).differentiable (by simp) p)
      |>.hasFDerivAt.hasFDerivWithinAt) (polar_inj a hrho) F).mp (hF.mono_set hPQ)
  simpa only [m64MorreyPolarStrip_det, abs_sq, smul_eq_mul, IntegrableOn, box_restrict] using hw

theorem m64MorreyPolarStrip_weighted_integral_le_annulus
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) {F : LoopPlane → ℝ}
    (hF : IntegrableOn F (Metric.closedBall a rho) volume) (hpos : ∀ p, 0 ≤ F p) :
    (∫ p in S, (rho * Real.exp (-p 1)) ^ 2 * F (m64MorreyPolarStrip a rho p)) ≤
      (∫ p in Metric.closedBall a rho, F p) -
        ∫ p in Metric.closedBall a (rho * Real.exp (-1)), F p := by
  let P := m64MorreyPolarStrip a rho
  have hinner : Metric.closedBall a (rho * Real.exp (-1)) ⊆ Metric.closedBall a rho :=
    Metric.closedBall_subset_closedBall
      (mul_le_of_le_one_right hrho.le (Real.exp_le_one_iff.mpr (by norm_num)))
  have hPQ : P '' Q ⊆ Metric.closedBall a rho \ Metric.closedBall a (rho * Real.exp (-1)) := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨m64MorreyPolarStrip_mapsTo_closedBall a hrho.le (box_subset hp), ?_⟩
    have hn : dist (P p) a = rho * Real.exp (-p 1) := by
      rw [dist_eq_norm]
      change ‖a + (rho * Real.exp (-p 1)) • Proofs.M58.angularPoint (p 0 - Real.pi) - a‖ = _
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by positivity),
        Proofs.M58.norm_angularPoint, mul_one]
    rw [Metric.mem_closedBall, hn, not_le]
    exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith [(box_mem hp).2.2.2])) hrho
  calc
    _ = ∫ p in Q, |(fderiv ℝ P p).det| • F (P p) := by
      simp only [P, m64MorreyPolarStrip_det, abs_sq, smul_eq_mul, box_restrict]
    _ = ∫ p in P '' Q, F p :=
      (integral_image_eq_integral_abs_det_fderiv_smul volume
        isOpen_m64AnnulusInterior.measurableSet
        (fun p _ => ((m64MorreyPolarStrip_contDiff a rho).differentiable (by simp) p)
          |>.hasFDerivAt.hasFDerivWithinAt) (polar_inj a hrho) F).symm
    _ ≤ ∫ p in Metric.closedBall a rho \ Metric.closedBall a (rho * Real.exp (-1)), F p :=
      setIntegral_mono_set (hF.mono_set sdiff_subset)
        (Eventually.of_forall hpos) (Eventually.of_forall hPQ)
    _ = _ := setIntegral_sdiff measurableSet_closedBall hF hinner

end PoincareConjecture
