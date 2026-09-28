import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.EquivalentInitial
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteHilbertOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

open SpectralHeatNative

variable {W H X : Type*} {m : ℕ}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [SeparableSpace X]

theorem exists_finite_equivalent_value_initial_heat
    (I : H →L[ℝ] X) (hIc : IsCompactOperator I) (hId : DenseRange I)
    (hIi : Function.Injective I) (e : W ≃L[ℝ] H)
    (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    {T M A C : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (he : ‖e.toContinuousLinearMap‖ ≤ M)
    (P : ℝ → H →L[ℝ] H) (hPc : ContinuousOn P (Icc 0 T))
    (hPb : ∀ t ∈ Icc 0 T, ‖P 0 - P t‖ ≤ A)
    (B : ℝ → H → H → ℝ) (hP : ∀ t u v, inner ℝ u (P t v) = B t u v)
    (hB : ∀ u v : W, inner ℝ u v =
      inner ℝ (I (e u)) (I (e v)) + B 0 (e u) (e v))
    (L : ℝ → PiLp 2 (fun _ : Fin m => H) →L[ℝ] PiLp 2 (fun _ : Fin m => X))
    (hLc : ContinuousOn L (Icc 0 T)) (hLb : ∀ t ∈ Icc 0 T, ‖L t‖ ≤ C)
    (hsmall : (T + 1) * (M * (A * M)) +
      (Real.sqrt T * (Real.sqrt T + 1)) * (C * M) < 1)
    (u₀ : PiLp 2 (fun _ : Fin m => X)) :
    ∃ (v : ℝ → PiLp 2 (fun _ : Fin m => H))
      (U : ℝ → PiLp 2 (fun _ : Fin m => X)),
      MemLp v 2 (timeMeasure T) ∧ U 0 = u₀ ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, finiteHilbertMap I (v t) = U t) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ w : PiLp 2 (fun _ : Fin m => H),
        HasDerivWithinAt (fun s => inner ℝ (finiteHilbertMap I w) (U s))
          (inner ℝ (finiteHilbertMap I w) (L t (v t)) -
            ∑ i, B t (w i) (v t i)) (Icc 0 T) t) ∧
      (∀ t ∈ Icc 0 T, ∀ w : PiLp 2 (fun _ : Fin m => H),
        inner ℝ (finiteHilbertMap I w) (U t) = inner ℝ (finiteHilbertMap I w) u₀ +
          ∫ s in (0 : ℝ)..t, inner ℝ (finiteHilbertMap I w) (L s (v s)) -
            ∑ i, B s (w i) (v s i)) := by
  let IV := finiteHilbertMap (m := m) I
  let E := finiteHilbertEquiv (m := m) e
  have hIn : ‖IV.comp E.toContinuousLinearMap‖ ≤ 1 := by
    change ‖(finiteHilbertMap I).comp (finiteHilbertMap e.toContinuousLinearMap)‖ ≤ 1
    rw [← finiteHilbertMap_comp]
    exact (norm_finiteHilbertMap_le _).trans hJn
  have hEn : ‖E.toContinuousLinearMap‖ ≤ M :=
    (norm_finiteHilbertMap_le e.toContinuousLinearMap).trans he
  let BV := fun u v : PiLp 2 (fun _ : Fin m => H) => ∑ i, B 0 (u i) (v i)
  have hBV (u v : PiLp 2 (fun _ : Fin m => W)) :
      inner ℝ u v = inner ℝ (IV (E u)) (IV (E v)) + BV (E u) (E v) := by
    simp only [PiLp.inner_apply, IV, E, BV, finiteHilbertMap_apply, finiteHilbertEquiv_apply]
    simp_rw [hB]
    exact Finset.sum_add_distrib
  let R : ℝ → PiLp 2 (fun _ : Fin m => H) →L[ℝ] PiLp 2 (fun _ : Fin m => H) :=
    fun t => finiteHilbertMapOperator (P 0 - P t)
  have hRc : ContinuousOn R (Icc 0 T) :=
    finiteHilbertMapOperator.continuous.comp_continuousOn (continuousOn_const.sub hPc)
  have hRb : ∀ t ∈ Icc 0 T, ‖R t‖ ≤ A :=
    fun t ht => (norm_finiteHilbertMap_le (P 0 - P t)).trans (hPb t ht)
  obtain ⟨v, U, hv, hU0, hUc, hUv, hweak, hUi⟩ :=
    exists_equivalent_value_initial_heat IV
      (finiteHilbertMap_compact _ hIc) (finiteHilbertMap_denseRange _ hId)
      (finiteHilbertMap_injective _ hIi) E hIn BV hBV hT hM hA hC hEn
      R hRc hRb L hLc hLb hsmall u₀
  have hp (w : PiLp 2 (fun _ : Fin m => H)) (t : ℝ) :
      inner ℝ w (R t (v t)) = BV w (v t) -
      ∑ i, B t (w i) (v t i) := by
    simp only [R, BV, finiteHilbertMapOperator_apply, PiLp.inner_apply,
      finiteHilbertMap_apply, sub_apply, inner_sub_right, Finset.sum_sub_distrib, hP]
  refine ⟨v, U, hv, hU0, hUc, hUv, ?_, ?_⟩
  · filter_upwards [hweak] with t ht
    intro w
    apply (ht w).congr_deriv
    rw [hp]
    ring
  · intro t ht w
    rw [hUi t ht w]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    change inner ℝ w (R s (v s)) + inner ℝ (IV w) (L s (v s)) - BV w (v s) = _
    rw [hp]
    ring

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
