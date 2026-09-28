import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityAveragingBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real











set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff SchwartzMap InnerProductSpace

namespace PoincareConjecture.M65Interior

private theorem averagingRadiusField_bounds
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane)) {r : ℝ} (hr : 0 < r)
    (x : LoopPlane) :
    MemLp (fun z => ∑ i : Fin 2, ((x i - z i) / r) * d i z) 2
      (volume.restrict (closedBall x r)) ∧
    ∀ z ∈ closedBall x r,
      (∑ i : Fin 2, ((x i - z i) / r) * d i z) ^ 2 ≤
        2 * ∑ i : Fin 2, (d i z) ^ 2 := by
  have hweight (i : Fin 2) (z : LoopPlane) (hz : z ∈ closedBall x r) :
      ‖(x i - z i) / r‖ ≤ 1 := by
    have hi := PiLp.norm_apply_le (x - z) i
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at hi
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr]
    exact (div_le_one hr).mpr (hi.trans (mem_closedBall_iff_norm'.mp hz))
  have hterm (i : Fin 2) (z : LoopPlane) (hz : z ∈ closedBall x r) :
      ‖((x i - z i) / r) * d i z‖ ≤ ‖d i z‖ := by
    rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hweight i z hz) (norm_nonneg (d i z))
  have hm (i : Fin 2) : MemLp (fun z => ((x i - z i) / r) * d i z) 2
      (volume.restrict (closedBall x r)) := by
    apply ((Lp.memLp (d i)).mono_measure Measure.restrict_le_self).of_le
    · have hc : Continuous (fun z : LoopPlane => (x i - z i) / r) := by fun_prop
      exact hc.aestronglyMeasurable.mul
        ((Lp.memLp (d i)).1.mono_measure Measure.restrict_le_self)
    · exact ae_restrict_of_forall_mem isClosed_closedBall.measurableSet (hterm i)
  refine ⟨by
    simpa +instances only [Fin.sum_univ_two, Pi.add_apply] using! (hm 0).add (hm 1), ?_⟩
  intro z hz
  have hs (i : Fin 2) : (((x i - z i) / r) * d i z) ^ 2 ≤ (d i z) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hterm i z hz)
  simp only [Fin.sum_univ_two]
  nlinarith only [hs 0, hs 1,
    sq_nonneg (((x 0 - z 0) / r) * d 0 z - ((x 1 - z 1) / r) * d 1 z)]




theorem averagingValue_derivative_sq_bounds {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ z, averagingProfile z ≤ B)
    (u : Lp ℝ 2 (volume : Measure LoopPlane))
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hw : ∀ i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i)))
    {r : ℝ} (hr : 0 < r) (x : LoopPlane) :
    (∀ i : Fin 2,
      (fderiv ℝ (averagingValue u r) x (EuclideanSpace.basisFun (Fin 2) ℝ i)) ^ 2 ≤
        2 * B * r⁻¹ ^ 2 * ∫ z in closedBall x r, ∑ j : Fin 2, (d j z) ^ 2) ∧
    (deriv (fun s => averagingValue u s x) r) ^ 2 ≤
      2 * B * r⁻¹ ^ 2 * ∫ z in closedBall x r, ∑ j : Fin 2, (d j z) ^ 2 := by
  let E := ∫ z in closedBall x r, ∑ j : Fin 2, (d j z) ^ 2
  have hi (i : Fin 2) : MemLp (d i) 2 (volume.restrict (closedBall x r)) :=
    (Lp.memLp (d i)).mono_measure Measure.restrict_le_self
  have hEint : IntegrableOn (fun z => ∑ j : Fin 2, (d j z) ^ 2) (closedBall x r) := by
    simpa +instances only [Fin.sum_univ_two, Pi.add_apply, IntegrableOn] using!
      (hi 0).integrable_sq.add (hi 1).integrable_sq
  have hE0 : 0 ≤ E := integral_nonneg (fun z => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  constructor
  · intro i
    have heq : fderiv ℝ (averagingValue u r) x (EuclideanSpace.basisFun (Fin 2) ℝ i) =
        averagingValue (d i) r x := by
      rw [averagingValue_fderiv_of_weak u d hw hr x i]
      exact integral_congr_ae (ae_of_all _ (fun _ => mul_comm _ _))
    rw [heq]
    have hcoord : (∫ z in closedBall x r, (d i z) ^ 2) ≤ E := by
      apply integral_mono_ae (hi i).integrable_sq hEint
      exact ae_of_all _ (fun z => Finset.single_le_sum
        (fun j _ => sq_nonneg (d j z)) (Finset.mem_univ i))
    have h := (averagingValue_sq_le hB hr x (hi i)).trans
      (mul_le_mul_of_nonneg_left hcoord (mul_nonneg hB0 (sq_nonneg _)))
    have hp : 0 ≤ B * r⁻¹ ^ 2 * E := by positivity
    change averagingValue (d i) r x ^ 2 ≤ 2 * B * r⁻¹ ^ 2 * E
    linarith only [h, hp]
  · let f : LoopPlane → ℝ := fun z => ∑ i : Fin 2, ((x i - z i) / r) * d i z
    obtain ⟨hf, hfsq⟩ := averagingRadiusField_bounds d hr x
    have heq : deriv (fun s => averagingValue u s x) r = -averagingValue f r x := by
      rw [(averagingValue_radius_of_weak u d hw hr x).deriv]
      congr 1
      exact integral_congr_ae (ae_of_all _ (fun _ => mul_comm _ _))
    rw [heq, neg_sq]
    have hfield : (∫ z in closedBall x r, f z ^ 2) ≤ 2 * E := by
      rw [show 2 * E = ∫ z in closedBall x r, 2 * ∑ i : Fin 2, (d i z) ^ 2 from
        (integral_const_mul _ _).symm]
      apply integral_mono_ae hf.integrable_sq (hEint.const_mul 2)
      exact ae_restrict_of_forall_mem isClosed_closedBall.measurableSet hfsq
    have h := (averagingValue_sq_le hB hr x hf).trans
      (mul_le_mul_of_nonneg_left hfield (mul_nonneg hB0 (sq_nonneg _)))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h

private theorem abs_le_power_of_sq_bound {B Λ β r v : ℝ} (hB : 0 ≤ B)
    (hΛ : 0 ≤ Λ) (hr : 0 < r)
    (hv : v ^ 2 ≤ 2 * B * r⁻¹ ^ 2 * (Λ * r ^ (2 * β))) :
    |v| ≤ (1 + B + Λ) * r ^ (β - 1) := by
  have hp : (r ^ (β - 1)) ^ 2 = r⁻¹ ^ 2 * r ^ (2 * β) := by
    rw [Real.rpow_sub_one hr.ne', div_pow]
    have hpβ : (r ^ β) ^ 2 = r ^ (2 * β) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hr.le]
      congr 1
      ring
    rw [hpβ]
    ring
  have hC : 2 * B * Λ ≤ (1 + B + Λ) ^ 2 := by
    nlinarith only [sq_nonneg (B - Λ), hB, hΛ, mul_nonneg hB hΛ]
  apply abs_le_of_sq_le_sq _ (mul_nonneg (by linarith) (Real.rpow_nonneg hr.le _))
  calc
    v ^ 2 ≤ 2 * B * r⁻¹ ^ 2 * (Λ * r ^ (2 * β)) := hv
    _ = (2 * B * Λ) * (r ^ (β - 1)) ^ 2 := by rw [hp]; ring
    _ ≤ (1 + B + Λ) ^ 2 * (r ^ (β - 1)) ^ 2 :=
      mul_le_mul_of_nonneg_right hC (sq_nonneg _)
    _ = ((1 + B + Λ) * r ^ (β - 1)) ^ 2 := by ring





theorem averagingValue_derivatives_of_energy {Λ β : ℝ} (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : Lp ℝ 2 (volume : Measure LoopPlane))
        (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane)),
      (∀ i (φ : 𝓢(LoopPlane, ℝ)),
        ⟪d i, φ.toLp 2 volume⟫_ℝ =
          -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.basisFun (Fin 2) ℝ i))) →
      ∀ (x : LoopPlane) (r : ℝ), 0 < r →
      (∫ z in closedBall x r, ∑ i : Fin 2, (d i z) ^ 2) ≤ Λ * r ^ (2 * β) →
      (∀ i : Fin 2,
        |fderiv ℝ (averagingValue u r) x (EuclideanSpace.basisFun (Fin 2) ℝ i)| ≤
          C * r ^ (β - 1)) ∧
        |deriv (fun s => averagingValue u s x) r| ≤ C * r ^ (β - 1) := by
  obtain ⟨B, hB0, hB⟩ := averagingProfile_bounded
  refine ⟨1 + B + Λ, by linarith, ?_⟩
  intro u d hw x r hr hE
  obtain ⟨hs, ht⟩ := averagingValue_derivative_sq_bounds hB0.le hB u d hw hr x
  have hE' := mul_le_mul_of_nonneg_left hE
    (show 0 ≤ 2 * B * r⁻¹ ^ 2 by positivity)
  exact ⟨fun i => abs_le_power_of_sq_bound hB0.le hΛ hr ((hs i).trans hE'),
    abs_le_power_of_sq_bound hB0.le hΛ hr (ht.trans hE')⟩

end PoincareConjecture.M65Interior
