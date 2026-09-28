import PoincareConjecture.Proofs.M35.Uniqueness.Heat.NonautonomousMixedHeat









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

omit [CompleteSpace V] [CompleteSpace H] [SeparableSpace H] in
private theorem memLp_timeDependent_const
    {T C : ℝ} (A : ℝ → V →L[ℝ] H) (hAm : AEStronglyMeasurable A (timeMeasure T))
    (hAb : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ C) (u : V) :
    MemLp (fun t => A t u) 2 (timeMeasure T) := by
  have hu : MemLp (fun _ : ℝ => u) 2 (timeMeasure T) := memLp_const u
  have h := memLp_timeDependent_apply hAm hAb (hu.toLp (fun _ => u))
  apply (memLp_congr_ae ?_).mp h
  filter_upwards [hu.coeFn_toLp] with t ht
  rw [ht]

theorem exists_nonautonomous_mixed_initial_heat
    (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T A C : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (R : ℝ → V →L[ℝ] V) (hRm : AEStronglyMeasurable R (timeMeasure T))
    (hRb : ∀ᵐ t ∂timeMeasure T, ‖R t‖ ≤ A)
    (L : ℝ → V →L[ℝ] H) (hLm : AEStronglyMeasurable L (timeMeasure T))
    (hLb : ∀ᵐ t ∂timeMeasure T, ‖L t‖ ≤ C)
    (hsmall : (T + 1) * A + (Real.sqrt T * (Real.sqrt T + 1)) * C < 1)
    (v₀ : V) :
    ∃ (v : ℝ → V) (U : ℝ → H),
      MemLp v 2 (timeMeasure T) ∧ U 0 = J v₀ ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
      (∀ᵐ t ∂timeMeasure T, ∀ w : V,
        HasDerivWithinAt (fun s => inner ℝ (J w) (U s))
          (inner ℝ w (R t (v t)) + inner ℝ (J w) (L t (v t)) -
            (inner ℝ w (v t) - inner ℝ (J w) (J (v t)))) (Icc 0 T) t) := by
  let F : ℝ → V := fun t => R t v₀ + J.adjoint (L t v₀) - (v₀ - J.adjoint (J v₀))
  have hF : MemLp F 2 (timeMeasure T) :=
    ((memLp_timeDependent_const R hRm hRb v₀).add
      (J.adjoint.comp_memLp' (memLp_timeDependent_const L hLm hLb v₀))).sub
        (memLp_const (v₀ - J.adjoint (J v₀)))
  obtain ⟨v, U, hU0, hUc, hUv, hweak⟩ :=
    exists_nonautonomous_mixed_heat J hc hd hi hn hT hA hC R hRm hRb
      L hLm hLb hsmall (hF.toLp F)
  refine ⟨fun t => v t + v₀, fun t => U t + J v₀,
    (Lp.memLp v).add (memLp_const v₀), ?_, hUc.add continuousOn_const, ?_, ?_⟩
  · change U 0 + J v₀ = J v₀
    rw [hU0, zero_add]
  · filter_upwards [hUv] with t ht
    rw [map_add, ht]
  · filter_upwards [hweak, hF.coeFn_toLp] with t ht hFt
    intro w
    have h := ht w
    have hdw : HasDerivWithinAt (fun s => inner ℝ (J w) (U s + J v₀))
        (inner ℝ w (R t (v t) + (hF.toLp F) t) + inner ℝ (J w) (L t (v t)) -
          (inner ℝ w (v t) - inner ℝ (J w) (J (v t)))) (Icc 0 T) t := by
      simpa only [inner_add_right] using! h.add_const (inner ℝ (J w) (J v₀))
    apply hdw.congr_deriv
    rw [hFt]
    dsimp only [F]
    simp only [map_add, inner_add_right, inner_sub_right, J.adjoint_inner_right]
    ring

end PoincareConjecture.M35.Uniqueness.Heat
