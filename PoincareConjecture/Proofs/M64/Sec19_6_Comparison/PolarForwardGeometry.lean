import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PolarForwardMap
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.ProjectionIntegrability
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration
import PoincareConjecture.Proofs.M60.Mathlib.NullSphere
import Mathlib.MeasureTheory.Function.Jacobian











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

open Proofs.M58




def m64PolarSource : Set LoopPlane :=
  {p | 0 < p 0 ∧ p 0 < curvePeriod ∧ 0 < p 1 ∧ p 1 < 1}




theorem m64PolarSource_open : IsOpen m64PolarSource := by
  have h0 := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have h1 := PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  exact (isOpen_lt continuous_const h0).inter
    ((isOpen_lt h0 continuous_const).inter
      ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 continuous_const)))




theorem m64PolarSource_subset : m64PolarSource ⊆ m64AnnulusDomain :=
  fun _ hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩




theorem m64PolarSource_ae_eq_domain : m64PolarSource =ᵐ[volume] m64AnnulusDomain := by
  have heq : m64PolarSource =
      (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹' (Set.pi Set.univ
        (fun i : Fin 2 => Set.Ioo ((0 : Fin 2 → ℝ) i) (![curvePeriod, 1] i))) := by
    ext p
    simp [m64PolarSource, Set.mem_pi, Fin.forall_fin_two, and_assoc]
  rw [heq]
  exact m64AnnulusDomain_ae_eq_boxInterior.symm




theorem m64PolarForwardMap_norm {p : LoopPlane} (hp : -1 < p 1) :
    ‖m64PolarForwardMap p‖ = (1 / 2 : ℝ) * (p 1 + 1) := by
  have hr : 0 < (1 / 2 : ℝ) * (p 1 + 1) := by linarith
  rw [m64PolarForwardMap, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    norm_angularPoint, mul_one]




theorem m64PolarForwardMap_injOn : InjOn m64PolarForwardMap m64PolarSource := by
  intro p hp q hq heq
  have hp1 : -1 < p 1 := by linarith [hp.2.2.1]
  have hq1 : -1 < q 1 := by linarith [hq.2.2.1]
  have hn := congrArg norm heq
  rw [m64PolarForwardMap_norm hp1, m64PolarForwardMap_norm hq1] at hn
  have hcoord1 : p 1 = q 1 := by linarith
  have hr : (1 / 2 : ℝ) * (p 1 + 1) ≠ 0 := ne_of_gt (by linarith [hp.2.2.1])
  have hang : angularPoint (p 0) = angularPoint (q 0) := by
    have heq' : ((1 / 2 : ℝ) * (p 1 + 1)) • angularPoint (p 0) =
        ((1 / 2 : ℝ) * (p 1 + 1)) • angularPoint (q 0) := by
      simpa only [m64PolarForwardMap, ← hcoord1] using heq
    have h := congrArg (fun w : LoopPlane =>
      (((1 / 2 : ℝ) * (p 1 + 1))⁻¹) • w) heq'
    simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using h
  have hexp : Circle.exp (p 0) = Circle.exp (q 0) := by
    rw [← m60LoopCircleHomeomorphCircle_angular, ← m60LoopCircleHomeomorphCircle_angular]
    exact congrArg m60LoopCircleHomeomorphCircle (Subtype.ext hang)
  have hcoord0 : p 0 = q 0 :=
    Circle.exp_injOn_Ico (a := 0) (b := curvePeriod) (by simp [curvePeriod])
      ⟨hp.1.le, hp.2.1⟩ ⟨hq.1.le, hq.2.1⟩ hexp
  ext i
  fin_cases i
  · exact hcoord0
  · exact hcoord1




theorem m64PolarForwardMap_image_subset :
    m64PolarForwardMap '' m64PolarSource ⊆
      (closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ loopDiskSet := by
  rintro _ ⟨p, hp, rfl⟩
  have hp1 : -1 < p 1 := by linarith [hp.2.2.1]
  have hn := m64PolarForwardMap_norm hp1
  simp only [mem_inter_iff, mem_compl_iff, mem_closedBall, dist_zero_right,
    loopDiskSet, not_le, hn]
  constructor <;> linarith [hp.2.2.1, hp.2.2.2]




theorem m64_horizontal_line_null : volume {z : LoopPlane | z 1 = 0} = 0 := by
  let S : Set (ℝ × ℝ) := univ ×ˢ {(0 : ℝ)}
  have hS : NullMeasurableSet S volume := by measurability
  have hzero : volume S = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have heq : loopPlaneEquivProd ⁻¹' S = {z : LoopPlane | z 1 = 0} := by
    ext z
    simp [S, loopPlaneEquivProd, MeasurableEquiv.finTwoArrow_apply]
  rw [← heq, measurePreserving_loopPlaneEquivProd.measure_preimage hS, hzero]




theorem m64_exists_open_polar_angle {z : LoopPlane} (hz : z ≠ 0) (hline : z 1 ≠ 0) :
    ∃ theta ∈ Ioo (0 : ℝ) curvePeriod, ‖z‖ • angularPoint theta = z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let q : LoopCircle := ⟨‖z‖⁻¹ • z, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']⟩
  obtain ⟨theta, htheta, hang⟩ := exists_angularPoint q
  have hzero : theta ≠ 0 := by
    intro ht
    have h := congrArg (fun w : LoopPlane => w 1) hang
    change (angularPoint theta) 1 = ‖z‖⁻¹ * z 1 at h
    simp only [ht, angularPoint, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Real.sin_zero] at h
    exact (mul_ne_zero (inv_ne_zero hn.ne') hline) h.symm
  have hperiod : theta ≠ curvePeriod := by
    intro ht
    have h := congrArg (fun w : LoopPlane => w 1) hang
    change (angularPoint theta) 1 = ‖z‖⁻¹ * z 1 at h
    simp only [ht, angularPoint, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      curvePeriod, Real.sin_two_pi] at h
    exact (mul_ne_zero (inv_ne_zero hn.ne') hline) h.symm
  refine ⟨theta, ⟨lt_of_le_of_ne htheta.1 hzero.symm,
    lt_of_le_of_ne htheta.2 hperiod⟩, ?_⟩
  rw [hang]
  exact smul_inv_smul₀ hn.ne' z




theorem m64PolarForwardMap_image_ae_eq :
    m64PolarForwardMap '' m64PolarSource =ᵐ[volume]
      ((closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ loopDiskSet : Set LoopPlane) := by
  filter_upwards [compl_mem_ae_iff.mpr m64_horizontal_line_null,
    M60.haar_ball_ae_eq_closedBall volume (0 : LoopPlane) 1] with z hline hball
  apply propext
  refine ⟨fun hz => m64PolarForwardMap_image_subset hz, ?_⟩
  intro hz
  have hlo : 1 / 2 < ‖z‖ := by
    simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz.1
  have hhi : ‖z‖ < 1 := mem_ball_zero_iff.mp (hball.mpr hz.2)
  have hn : z ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨theta, htheta, hang⟩ := m64_exists_open_polar_angle hn hline
  refine ⟨annulusPoint theta (2 * ‖z‖ - 1),
    ⟨htheta.1, htheta.2, by change 0 < 2 * ‖z‖ - 1; linarith,
      by change 2 * ‖z‖ - 1 < 1; linarith⟩, ?_⟩
  change ((1 / 2 : ℝ) * (2 * ‖z‖ - 1 + 1)) • angularPoint theta = z
  have hrad : (1 / 2 : ℝ) * (2 * ‖z‖ - 1 + 1) = ‖z‖ := by ring
  rw [hrad]
  exact hang

end PoincareConjecture
