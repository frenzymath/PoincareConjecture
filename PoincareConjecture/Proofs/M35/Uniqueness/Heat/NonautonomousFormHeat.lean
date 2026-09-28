import PoincareConjecture.Proofs.M35.Uniqueness.Heat.TimeDependentOperator
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormValueTrace
import Mathlib.MeasureTheory.Measure.OpenPos










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

omit [SeparableSpace H] in
theorem adjoint_value_trace_eq (J : V →L[ℝ] H)
    {T : ℝ} {U : ℝ → H} {P : ℝ → V}
    (hU0 : U 0 = 0) (hP0 : P 0 = 0)
    (hUc : ContinuousOn U (Icc (0 : ℝ) T)) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hae : (fun t => J.adjoint (U t)) =ᵐ[timeMeasure T] P) :
    ∀ t ∈ Icc (0 : ℝ) T, J.adjoint (U t) = P t := by
  have he := Measure.eqOn_Ioc_of_ae_eq (volume : Measure ℝ) hae
    ((J.adjoint.continuous.comp_continuousOn hUc).mono Ioc_subset_Icc_self)
    (hPc.mono Ioc_subset_Icc_self)
  intro t ht
  rcases ht.1.eq_or_lt with rfl | hpos
  · rw [hU0, hP0, map_zero]
  · exact he ⟨hpos, ht.2⟩



theorem exists_nonautonomous_form_heat (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (A : ℝ → V →L[ℝ] V) (hA : AEStronglyMeasurable A (timeMeasure T))
    (hb : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ C) (hsmall : (T + 1) * C < 1)
    (F : Lp V 2 (timeMeasure T)) :
    ∃ (v : Lp V 2 (timeMeasure T)) (U : ℝ → H),
      U 0 = 0 ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ w : V,
        HasDerivWithinAt (fun s => inner ℝ (J w) (U s))
          (inner ℝ w (A t (v t) + F t) -
            (inner ℝ w (v t) - inner ℝ (J w) (J (v t)))) (Icc 0 T) t) := by
  let R := timeDependentLpOperator hA hb
  have hR : (T + 1) * ‖R‖ < 1 :=
    (mul_le_mul_of_nonneg_left (norm_timeDependentLpOperator_le hA hb hC)
      (by positivity)).trans_lt hsmall
  obtain ⟨v, P, D, hP0, hPc, hD, hderiv, hgraph, heq, hv⟩ :=
    exists_perturbed_form_heat J hc hd hi hn hT R hR F
  obtain ⟨U, hU0, hUc, hUv, _⟩ := formWeakHeat_value_trace J hc hd hi hn hT (R v + F)
  rw [hv] at hUv
  have hUP : ∀ t ∈ Icc (0 : ℝ) T, J.adjoint (U t) = P t := by
    apply adjoint_value_trace_eq J hU0 hP0 hUc hPc
    filter_upwards [hUv, hgraph] with t ht hp
    rw [← ht, hp]
  refine ⟨v, U, hU0, hUc, hUv, ?_⟩
  filter_upwards [hderiv, heq, hgraph, timeDependentLpOperator_coe hA hb v,
    Lp.coeFn_add (R v) F, ae_restrict_mem measurableSet_Ioc] with t ht he hg hAv hsum htime
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
  have hscalar := congrArg (fun z => inner ℝ w z) he
  rw [hsum, Pi.add_apply, hAv, inner_add_right, inner_sub_right,
    inner_add_right, ← hg, J.adjoint_inner_right] at hscalar
  convert htest using 1
  rw [inner_add_right]
  linarith only [hscalar]

end PoincareConjecture.M35.Uniqueness.Heat
