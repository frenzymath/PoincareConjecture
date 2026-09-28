import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Regularity
import Mathlib.Topology.Order.IntermediateValue



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def criticalPolynomial (z : Real) : Real :=
  (1 - z^2) * (2*z - 1)^2 - (9 / 100) * z^2



theorem exists_critical_latitude :
    ∃ z : Real, (3 / 5 : Real) < z ∧ z < 5 / 8 ∧
      Real.sqrt (1 - z^2) * (2*z - 1) = (3 / 10) * z := by
  have hcont : Continuous criticalPolynomial := by unfold criticalPolynomial; fun_prop
  have hlo : criticalPolynomial (3 / 5) < 0 := by norm_num [criticalPolynomial]
  have hhi : 0 < criticalPolynomial (5 / 8) := by norm_num [criticalPolynomial]
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc
    (by norm_num : (3 / 5 : Real) ≤ 5 / 8) hcont.continuousOn ⟨hlo.le, hhi.le⟩
  have hl : (3 / 5 : Real) < z := lt_of_le_of_ne hz.1 (by
    intro he
    rw [← he] at hzero
    linarith)
  have hu : z < (5 / 8 : Real) := lt_of_le_of_ne hz.2 (by
    intro he
    rw [he] at hzero
    linarith)
  have hrad : 0 ≤ 1 - z^2 := by nlinarith
  have hs := Real.sq_sqrt hrad
  have hsq : (Real.sqrt (1 - z^2) * (2*z - 1))^2 = ((3 / 10) * z)^2 := by
    rw [mul_pow, hs]
    dsimp [criticalPolynomial] at hzero
    nlinarith
  refine ⟨z, hl, hu, (sq_eq_sq₀ ?_ ?_).mp hsq⟩
  · exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  · positivity

private theorem upperRoot_gt_five_eighths : (5 / 8 : Real) < upperRoot := by
  have hs := Real.sq_sqrt (by norm_num : (0 : Real) ≤ 19)
  have hn := Real.sqrt_nonneg (19 : Real)
  have hbound : (17 / 4 : Real) < Real.sqrt 19 := by nlinarith
  dsimp [upperRoot]
  linarith



theorem exists_critical_point_above_nested_cut :
    ∃ p : S2,
      (3 / 5 : Real) < (p : E3) 2 ∧ (p : E3) 2 < 5 / 8 ∧
      (p : E3) 0 < 0 ∧ (p : E3) 1 = 0 ∧
      mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 ∧ 1 < height p := by
  obtain ⟨z, hl, hu, hcrit⟩ := exists_critical_latitude
  have hrad : 0 < 1 - z^2 := by nlinarith
  let x := -Real.sqrt (1 - z^2)
  have hx : x < 0 := neg_neg_of_pos (Real.sqrt_pos.mpr hrad)
  have hxz : x^2 + z^2 = 1 := by
    dsimp [x]
    rw [neg_sq, Real.sq_sqrt hrad.le]
    ring
  have hrel : x * (2*z - 1) + (3 / 10) * z = 0 := by
    dsimp [x]
    nlinarith [hcrit]
  let p : S2 := ⟨vector x 0 z, by
    rw [mem_sphere_zero_iff_norm]
    have hn := EuclideanSpace.norm_sq_eq (vector x 0 z)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
    nlinarith [norm_nonneg (vector x 0 z)]⟩
  have hp0 : (p : E3) 0 = x := by simp [p]
  have hp1 : (p : E3) 1 = 0 := by simp [p]
  have hp2 : (p : E3) 2 = z := by simp [p]
  have hpcrit : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0 := by
    apply (critical_iff_tangent p).mpr
    intro w hw
    have hinner : inner Real (p : E3) w = x*w 0 + z*w 2 := by
      simp [PiLp.inner_apply, Fin.sum_univ_three, hp0, hp1, hp2, mul_comm]
    rw [hinner] at hw
    rw [hp0, hp1]
    have heq : z * (w 2 + 2*x*w 0 + 2*0*w 1 + (3 / 10)*w 0) = 0 := by
      nlinarith [mul_eq_zero.mpr (Or.inl hrel :
        x * (2*z - 1) + (3 / 10) * z = 0 ∨ w 0 = 0)]
    exact (mul_eq_zero.mp heq).resolve_left (by linarith)
  have hneg : levelRadicand z < 0 := by
    apply lt_of_not_ge
    intro hn
    rcases (levelRadicand_nonneg_iff z).mp hn with hn | hn
    · linarith [hn.2]
    · linarith [hn.1, upperRoot_gt_five_eighths]
  have hab : levelAbscissa z < 0 := by
    unfold levelAbscissa
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (by linarith)) (by linarith)
  have hax : levelAbscissa z < x := by
    have hs : x^2 < (levelAbscissa z)^2 := by
      dsimp [levelRadicand] at hneg
      nlinarith
    nlinarith
  have hheight : 1 < height p := by
    rw [height_apply, hp0, hp1, hp2]
    dsimp [levelAbscissa] at hax
    nlinarith
  exact ⟨p, by simpa [hp2] using hl, by simpa [hp2] using hu,
    hp0 ▸ hx, hp1, hpcrit, hheight⟩

end Poincare.Manifold.Schoenflies.Saddle.Nested
