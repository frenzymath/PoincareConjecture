import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteHilbertOperator
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.MixedHeatEquivalent










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {W H X : Type*} {m : ℕ}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [SeparableSpace X]

theorem exists_finite_equivalent_mixed_initial_heat
    (I : H →L[ℝ] X) (hIc : IsCompactOperator I) (hId : DenseRange I)
    (hIi : Function.Injective I) (e : W ≃L[ℝ] H)
    (hJn : ‖I.comp e.toContinuousLinearMap‖ ≤ 1)
    {b : ℝ} (hb : 0 < b) (P : ℝ → H →L[ℝ] H)
    (hPc : ContinuousOn P (Icc 0 b))
    (B : ℝ → H → H → ℝ) (hP : ∀ t u v, inner ℝ u (P t v) = B t u v)
    (hB : ∀ u v : W, inner ℝ u v =
      inner ℝ (I (e u)) (I (e v)) + B 0 (e u) (e v))
    (L : ℝ → PiLp 2 (fun _ : Fin m => H) →L[ℝ] PiLp 2 (fun _ : Fin m => X))
    (hLc : ContinuousOn L (Icc 0 b)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ T < b ∧
      ∀ v₀ : PiLp 2 (fun _ : Fin m => H),
      ∃ (v : ℝ → PiLp 2 (fun _ : Fin m => H))
        (U : ℝ → PiLp 2 (fun _ : Fin m => X)),
        MemLp v 2 (timeMeasure T) ∧ U 0 = finiteHilbertMap I v₀ ∧
        ContinuousOn U (Icc 0 T) ∧
        (∀ᵐ t ∂timeMeasure T, finiteHilbertMap I (v t) = U t) ∧
        (∀ᵐ t ∂timeMeasure T, ∀ w : PiLp 2 (fun _ : Fin m => H),
          HasDerivWithinAt (fun s => inner ℝ (finiteHilbertMap I w) (U s))
            (inner ℝ (finiteHilbertMap I w) (L t (v t)) -
              ∑ i, B t (w i) (v t i)) (Icc 0 T) t) := by
  let IV := finiteHilbertMap (m := m) I
  let E := finiteHilbertEquiv (m := m) e
  have hIn : ‖IV.comp E.toContinuousLinearMap‖ ≤ 1 := by
    change ‖(finiteHilbertMap I).comp (finiteHilbertMap e.toContinuousLinearMap)‖ ≤ 1
    rw [← finiteHilbertMap_comp]
    exact (norm_finiteHilbertMap_le _).trans hJn
  let BV := fun u v : PiLp 2 (fun _ : Fin m => H) => ∑ i, B 0 (u i) (v i)
  have hBV (u v : PiLp 2 (fun _ : Fin m => W)) :
      inner ℝ u v = inner ℝ (IV (E u)) (IV (E v)) + BV (E u) (E v) := by
    simp only [PiLp.inner_apply, IV, E, BV, finiteHilbertMap_apply, finiteHilbertEquiv_apply]
    simp_rw [hB]
    exact Finset.sum_add_distrib
  let R : ℝ → PiLp 2 (fun _ : Fin m => H) →L[ℝ] PiLp 2 (fun _ : Fin m => H) :=
    fun t => finiteHilbertMapOperator (P 0 - P t)
  have hRc : ContinuousOn R (Icc 0 b) :=
    finiteHilbertMapOperator.continuous.comp_continuousOn (continuousOn_const.sub hPc)
  have hR0 : R 0 = 0 := by
    dsimp only [R]
    rw [sub_self, map_zero]
  obtain ⟨T, hT, hT1, hTb, hsol⟩ :=
    exists_equivalent_continuous_mixed_initial_heat IV
      (finiteHilbertMap_compact _ hIc) (finiteHilbertMap_denseRange _ hId)
      (finiteHilbertMap_injective _ hIi) E hIn BV hBV hb R hRc hR0 L hLc
  refine ⟨T, hT, hT1, hTb, ?_⟩
  intro v₀
  obtain ⟨v, U, hv, hU0, hUc, hUv, hweak⟩ := hsol v₀
  refine ⟨v, U, hv, hU0, hUc, hUv, ?_⟩
  filter_upwards [hweak] with t ht
  intro w
  have hp : inner ℝ w (R t (v t)) = BV w (v t) -
      ∑ i, B t (w i) (v t i) := by
    simp only [R, BV, finiteHilbertMapOperator_apply, PiLp.inner_apply,
      finiteHilbertMap_apply, sub_apply, inner_sub_right, Finset.sum_sub_distrib, hP]
  apply (ht w).congr_deriv
  rw [hp]
  ring

end PoincareConjecture.M35.Uniqueness.Heat
