import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormWeakHeat
import Mathlib.Topology.MetricSpace.Contracting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem exists_form_heat_of_contractive_response (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    (R : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (hR : ‖(formWeakHeatOperator J hc hd hi hn hT).comp R‖ < 1)
    (F : Lp V 2 (timeMeasure T)) :
    ∃ (v : Lp V 2 (timeMeasure T)) (P D : ℝ → V),
      P 0 = 0 ∧ ContinuousOn P (Icc (0 : ℝ) T) ∧ MemLp D 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt P (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T, J.adjoint (J (v t)) = P t) ∧
      (∀ᵐ t ∂timeMeasure T, D t + v t - P t = (R v + F) t) ∧
      formWeakHeatOperator J hc hd hi hn hT (R v + F) = v := by
  let S := formWeakHeatOperator J hc hd hi hn hT
  let L := S.comp R
  have hL : ‖L‖ < 1 := hR
  let N : Lp V 2 (timeMeasure T) → Lp V 2 (timeMeasure T) := fun v => L v + S F
  have hN : ContractingWith ‖L‖₊ N := by
    refine ⟨hL, LipschitzWith.of_dist_le_mul ?_⟩
    intro v w
    simpa only [N, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub, coe_nnnorm]
      using L.le_opNorm (v - w)
  let v := hN.fixedPoint N
  have hv : S (R v + F) = v := by
    have h : N v = v := hN.fixedPoint_isFixedPt
    calc
      S (R v + F) = N v := by simp only [N, L, ContinuousLinearMap.comp_apply, map_add]
      _ = v := h
  obtain ⟨P, D, hP0, hPc, hD, hderiv, hgraph, heq⟩ :=
    formWeakHeat_equation J hc hd hi hn hT (R v + F)
  refine ⟨v, P, D, hP0, hPc, hD, hderiv, ?_, ?_, hv⟩
  · change ∀ᵐ t ∂timeMeasure T, J.adjoint (J (S (R v + F) t)) = P t at hgraph
    rw [hv] at hgraph
    exact hgraph
  · change ∀ᵐ t ∂timeMeasure T, D t + S (R v + F) t - P t = (R v + F) t at heq
    rw [hv] at heq
    exact heq

theorem exists_perturbed_form_heat (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    (R : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (hR : (T + 1) * ‖R‖ < 1) (F : Lp V 2 (timeMeasure T)) :
    ∃ (v : Lp V 2 (timeMeasure T)) (P D : ℝ → V),
      P 0 = 0 ∧ ContinuousOn P (Icc (0 : ℝ) T) ∧ MemLp D 2 (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt P (D t) t) ∧
      (∀ᵐ t ∂timeMeasure T, J.adjoint (J (v t)) = P t) ∧
      (∀ᵐ t ∂timeMeasure T, D t + v t - P t = (R v + F) t) ∧
      formWeakHeatOperator J hc hd hi hn hT (R v + F) = v := by
  apply exists_form_heat_of_contractive_response J hc hd hi hn hT R ?_ F
  exact ((ContinuousLinearMap.opNorm_comp_le _ R).trans
    (mul_le_mul_of_nonneg_right (norm_formWeakHeatOperator_le J hc hd hi hn hT)
      (norm_nonneg R))).trans_lt hR

end PoincareConjecture.M35.Uniqueness.Heat
