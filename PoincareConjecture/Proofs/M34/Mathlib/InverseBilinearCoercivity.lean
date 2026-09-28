import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic












set_option autoImplicit false

open scoped BigOperators

namespace ContinuousLinearMap



theorem inverse_inner_coercive_of_coercive
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E →L[ℝ] E →L[ℝ] ℝ) (hG : G.IsInvertible)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (hGB : ‖G‖ ≤ B)
    (hcoerc : ∀ v, a * ‖v‖ ^ 2 ≤ G v v) (z : E) :
    (a / B ^ 2) * ‖z‖ ^ 2 ≤ (innerSL ℝ z) (G.inverse (innerSL ℝ z)) := by
  let v := G.inverse (innerSL ℝ z)
  have hv : G v = innerSL ℝ z := hG.self_apply_inverse _
  have hn : ‖z‖ ≤ B * ‖v‖ := by
    calc
      ‖z‖ = ‖G v‖ := by rw [hv, innerSL_apply_norm]
      _ ≤ ‖G‖ * ‖v‖ := G.le_opNorm v
      _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right hGB (norm_nonneg v)
  have hs : ‖z‖ ^ 2 ≤ B ^ 2 * ‖v‖ ^ 2 := by
    nlinarith only [mul_self_le_mul_self (norm_nonneg z) hn]
  have hc : a * ‖v‖ ^ 2 ≤ (innerSL ℝ z) v := by
    simpa only [hv] using hcoerc v
  have hh := (mul_le_mul_of_nonneg_left hs ha).trans
    (show a * (B ^ 2 * ‖v‖ ^ 2) ≤ B ^ 2 * (innerSL ℝ z) v by
      nlinarith only [mul_le_mul_of_nonneg_left hc (sq_nonneg B)])
  rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hB)]
  nlinarith only [hh]




theorem inverse_inner_eq_sum_coordinates
    {I : Type*} [Fintype I]
    (G : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ I) :
    (innerSL ℝ z) (G.inverse (innerSL ℝ z)) =
      ∑ i : I, ∑ j : I, (G.inverse (EuclideanSpace.proj j)) i * z i * z j := by
  have hz : innerSL ℝ z = ∑ j : I, z j • EuclideanSpace.proj j := by
    ext w
    simp [PiLp.inner_apply, mul_comm]
  rw [hz]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change z j * (z i * (G.inverse (EuclideanSpace.proj j)) i) = _
  ring




theorem inverse_sum_coordinates_coercive
    {I : Type*} [Fintype I]
    (G : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I →L[ℝ] ℝ) (hG : G.IsInvertible)
    {a B : ℝ} (ha : 0 ≤ a) (hB : 0 < B) (hGB : ‖G‖ ≤ B)
    (hcoerc : ∀ v, a * ‖v‖ ^ 2 ≤ G v v) (z : EuclideanSpace ℝ I) :
    (a / B ^ 2) * (∑ i : I, z i ^ 2) ≤
      ∑ i : I, ∑ j : I, (G.inverse (EuclideanSpace.proj j)) i * z i * z j := by
  have hh := inverse_inner_coercive_of_coercive G hG ha hB hGB hcoerc z
  rwa [inverse_inner_eq_sum_coordinates, EuclideanSpace.real_norm_sq_eq] at hh

end ContinuousLinearMap
