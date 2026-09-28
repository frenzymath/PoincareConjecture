import PoincareConjecture.Proofs.M35.Uniqueness.Heat.NonautonomousFormHeat
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormMixedHeat










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem exists_nonautonomous_mixed_heat (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T A C : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ A)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (hsmall : (T + 1) * A + (Real.sqrt T * (Real.sqrt T + 1)) * C < 1)
    (F : Lp V 2 (timeMeasure T)) :
    ∃ (v : Lp V 2 (timeMeasure T)) (U : ℝ → H),
      U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ w : V,
        HasDerivWithinAt (fun s => inner ℝ (J w) (U s))
          (inner ℝ w (R t (v t) + F t) + inner ℝ (J w) (L t (v t)) -
            (inner ℝ w (v t) - inner ℝ (J w) (J (v t)))) (Icc 0 T) t) := by
  let RR := timeDependentLpOperator hRm hRb
  let LL := timeDependentLpOperator hLm hLb
  let JA := J.adjoint.compLpL 2 (timeMeasure T)
  let M := RR + JA.comp LL
  have hmixed : (T + 1) * ‖RR‖ + (Real.sqrt T * (Real.sqrt T + 1)) * ‖LL‖ < 1 :=
    (add_le_add
      (mul_le_mul_of_nonneg_left (norm_timeDependentLpOperator_le hRm hRb hA) (by positivity))
      (mul_le_mul_of_nonneg_left (norm_timeDependentLpOperator_le hLm hLb hC)
        (by positivity))).trans_lt hsmall
  obtain ⟨v, P, D, hP0, hPc, hD, hdP, hgraph, heq, hv⟩ :=
    exists_mixed_perturbed_form_heat J hc hd hi hn hT RR LL hmixed F
  obtain ⟨U, hU0, hUc, hUv, _⟩ := formWeakHeat_value_trace J hc hd hi hn hT (M v + F)
  rw [hv] at hUv
  have hUP : ∀ t ∈ Icc (0 : ℝ) T, J.adjoint (U t) = P t := by
    apply adjoint_value_trace_eq J hU0 hP0 hUc hPc
    filter_upwards [hUv, hgraph] with t ht hp
    rw [← ht, hp]
  have hMv : M v = RR v + JA (LL v) := rfl
  have hMcoe : ∀ᵐ t ∂timeMeasure T, (M v) t =
      R t (v t) + J.adjoint (L t (v t)) := by
    rw [hMv]
    filter_upwards [Lp.coeFn_add (RR v) (JA (LL v)),
      timeDependentLpOperator_coe hRm hRb v, timeDependentLpOperator_coe hLm hLb v,
      J.adjoint.coeFn_compLpL (LL v)] with t hs hr hl hj
    rw [hs, Pi.add_apply, hr, hj, hl]
  refine ⟨v, U, hU0, hUc, hUv, ?_⟩
  filter_upwards [hdP, heq, hgraph, hMcoe, Lp.coeFn_add (M v) F,
    ae_restrict_mem measurableSet_Ioc] with t ht he hg hm hsum htime
  intro w
  have hp : ∀ s ∈ Icc (0 : ℝ) T,
      inner ℝ (J w) (U s) = inner ℝ w (P s) := by
    intro s hs
    rw [← hUP s hs, J.adjoint_inner_right]
  have hdw : HasDerivWithinAt (fun s => inner ℝ w (P s)) (inner ℝ w (D t))
      (Icc 0 T) t :=
    ((innerSL ℝ w).hasFDerivAt.comp_hasDerivAt t ht).hasDerivWithinAt
  have htest : HasDerivWithinAt (fun s => inner ℝ (J w) (U s))
      (inner ℝ w (D t)) (Icc 0 T) t :=
    hdw.congr_of_mem hp (Ioc_subset_Icc_self htime)
  have he' : D t + v t - P t = (M v + F) t := he
  have hs := congrArg (fun z => inner ℝ w z) he'
  rw [hsum, Pi.add_apply, hm, inner_add_right, inner_sub_right,
    inner_add_right, inner_add_right, ← hg, J.adjoint_inner_right,
    J.adjoint_inner_right] at hs
  apply htest.congr_deriv
  rw [inner_add_right]
  linarith only [hs]

end PoincareConjecture.M35.Uniqueness.Heat
