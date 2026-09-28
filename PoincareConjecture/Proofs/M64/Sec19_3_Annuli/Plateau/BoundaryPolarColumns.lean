import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryPolarPullback
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.StrongSquareOperations









noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M64

open Proofs.M58

local notation "S" => interior m64AnnulusDomain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




def boundaryAngularColumn (x r : ℝ) (V : Fin 2 → LoopPlane → E) (theta : ℝ) : E :=
  (-r * Real.sin theta) • V 0 (r • angularPoint theta + annulusPoint x 0) +
    (r * Real.cos theta) • V 1 (r • angularPoint theta + annulusPoint x 0)




def boundaryPolarColumn (x rho : ℝ) (V : Fin 2 → LoopPlane → E) (p : LoopPlane) : E :=
  boundaryAngularColumn x (rho * Real.exp (-p 1)) V (p 0 / 2)




theorem boundaryPolarColumn_eq (x rho : ℝ) (V : Fin 2 → LoopPlane → E) (p : LoopPlane) :
    boundaryPolarColumn x rho V p =
      (-rho * Real.exp (-p 1) * Real.sin (p 0 / 2)) • V 0 (boundaryPolarStrip x rho p) +
        (rho * Real.exp (-p 1) * Real.cos (p 0 / 2)) • V 1 (boundaryPolarStrip x rho p) := by
  simp only [boundaryPolarColumn, boundaryAngularColumn, boundaryPolarStrip, neg_mul, add_comm]

private theorem continuous_memLp_top (f : LoopPlane → ℝ) (hf : Continuous f) :
    MemLp f ∞ (volume.restrict S) := by
  obtain ⟨C, hC⟩ := m64AnnulusDomain_isCompact.exists_bound_of_continuousOn hf.continuousOn
  apply memLp_top_of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  exact hC p (interior_subset hp)




theorem boundaryPolarColumn_memLp (x : ℝ) {rho : ℝ} (hrho : 0 < rho)
    (V : Fin 2 → LoopPlane → E)
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (upperBoundaryShell x rho))) :
    MemLp (boundaryPolarColumn x rho V) 2 (volume.restrict S) := by
  have h0 := continuous_memLp_top
    (fun p : LoopPlane => -rho * Real.exp (-p 1) * Real.sin (p 0 / 2)) (by fun_prop)
  have h1 := continuous_memLp_top
    (fun p : LoopPlane => rho * Real.exp (-p 1) * Real.cos (p 0 / 2)) (by fun_prop)
  rw [show boundaryPolarColumn x rho V = (fun p =>
    (-rho * Real.exp (-p 1) * Real.sin (p 0 / 2)) • V 0 (boundaryPolarStrip x rho p) +
      (rho * Real.exp (-p 1) * Real.cos (p 0 / 2)) • V 1 (boundaryPolarStrip x rho p)) from
    funext (boundaryPolarColumn_eq x rho V)]
  exact (MemLp.smul (boundaryPolarStrip_memLp_two x hrho (hV 0)) h0).add
      (MemLp.smul (boundaryPolarStrip_memLp_two x hrho (hV 1)) h1)




theorem boundaryPolarColumn_norm_sq_le (x rho : ℝ) (V : Fin 2 → LoopPlane → E)
    (p : LoopPlane) :
    ‖boundaryPolarColumn x rho V p‖ ^ 2 ≤
      2 * (rho * Real.exp (-p 1)) ^ 2 *
        (‖V 0 (boundaryPolarStrip x rho p)‖ ^ 2 +
          ‖V 1 (boundaryPolarStrip x rho p)‖ ^ 2) := by
  let r := rho * Real.exp (-p 1)
  let t := p 0 / 2
  let W := fun i => V i (boundaryPolarStrip x rho p)
  let u := (-r * Real.sin t) • W 0
  let v := (r * Real.cos t) • W 1
  have hu : ‖u‖ ≤ |r| * ‖W 0‖ := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg r) (Real.abs_sin_le_one t)) (norm_nonneg _)
  have hv : ‖v‖ ≤ |r| * ‖W 1‖ := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg r) (Real.abs_cos_le_one t)) (norm_nonneg _)
  have hu2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hu
  have hv2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hv
  simp only [mul_pow, sq_abs] at hu2 hv2
  have hs := (sq_le_sq₀ (norm_nonneg (u + v))
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le u v)
  rw [boundaryPolarColumn_eq, neg_mul]
  change ‖u + v‖ ^ 2 ≤ 2 * r ^ 2 * (‖W 0‖ ^ 2 + ‖W 1‖ ^ 2)
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]




theorem boundaryPolarColumn_integral (x rho s : ℝ) (V : Fin 2 → LoopPlane → E) :
    (∫ t in Icc (0 : ℝ) curvePeriod,
      ‖boundaryPolarColumn x rho V (annulusPoint t s)‖ ^ 2) =
      2 * ∫ theta in Icc (0 : ℝ) Real.pi,
        ‖boundaryAngularColumn x (rho * Real.exp (-s)) V theta‖ ^ 2 := by
  have hT : (0 : ℝ) ≤ curvePeriod := by unfold curvePeriod; positivity
  change (∫ t in Icc (0 : ℝ) curvePeriod,
    ‖boundaryAngularColumn x (rho * Real.exp (-s)) V (t / 2)‖ ^ 2) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT,
    intervalIntegral.integral_comp_div
      (fun theta => ‖boundaryAngularColumn x (rho * Real.exp (-s)) V theta‖ ^ 2)
      (by norm_num : (2 : ℝ) ≠ 0)]
  rw [zero_div, show curvePeriod / 2 = Real.pi by unfold curvePeriod; ring,
    intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_Icc_eq_integral_Ioc]
  rfl

end PoincareConjecture.M64
