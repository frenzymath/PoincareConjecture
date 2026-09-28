import PoincareConjecture.Proofs.M35.Uniqueness.Heat.AffineInitialHeat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative

variable {P V H : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

theorem contDiffAt_affineInitialForm (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    (M : P → Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (F : P → Lp V 2 (timeMeasure T)) (u₀ : H) {p : P}
    (hM : ContDiffAt ℝ ∞ M p) (hF : ContDiffAt ℝ ∞ F p)
    (hsmall : ‖(formWeakHeatOperator J hc hd hi hn hT).comp (M p)‖ < 1) :
    ContDiffAt ℝ ∞ (fun s => affineInitialForm J hc hd hi hn hT (M s) (F s) u₀) p := by
  let S := formWeakHeatOperator J hc hd hi hn hT
  have hA : ContDiffAt ℝ ∞ (fun s => S.comp (M s)) p := contDiffAt_const.clm_comp hM
  have hq : ContDiffAt ℝ ∞
      (fun s => S (F s) + homogeneousInitialLp J hc hd hi hn hT u₀) p :=
    (S.contDiff.comp_contDiffAt p hF).add contDiffAt_const
  exact contDiffAt_affineResponse hA hq hsmall

theorem contDiffAt_affineInitialValue (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    (M : P → Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (F : P → Lp V 2 (timeMeasure T)) (u₀ : H) {p : P}
    (hM : ContDiffAt ℝ ∞ M p) (hF : ContDiffAt ℝ ∞ F p)
    (hsmall : ‖(formWeakHeatOperator J hc hd hi hn hT).comp (M p)‖ < 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiffAt ℝ ∞ (fun s => affineInitialValue J hc hd hi hn hT (M s) (F s) u₀ t) p := by
  have hv := contDiffAt_affineInitialForm J hc hd hi hn hT M F u₀ hM hF hsmall
  have hG : ContDiffAt ℝ ∞
      (fun s => M s (affineInitialForm J hc hd hi hn hT (M s) (F s) u₀) + F s) p :=
    (hM.clm_apply hv).add hF
  let E := (ContinuousMap.evalCLM ℝ (⟨t, ht⟩ : Icc (0 : ℝ) T)).comp
    (weakValuePathOperator J hc hd hi hn hT)
  exact (E.contDiff.comp_contDiffAt p hG).add contDiffAt_const

omit [NormedSpace ℝ P] in
theorem affineInitialValue_solution_eventually (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    (M : P → Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (F : P → Lp V 2 (timeMeasure T)) (u₀ : H) {p : P}
    (hM : ContinuousAt M p)
    (hsmall : ‖(formWeakHeatOperator J hc hd hi hn hT).comp (M p)‖ < 1) :
    ∀ᶠ s in 𝓝 p,
      let v := affineInitialForm J hc hd hi hn hT (M s) (F s) u₀
      let U := affineInitialValue J hc hd hi hn hT (M s) (F s) u₀
      U 0 = u₀ ∧ ContinuousOn U (Icc 0 T) ∧
        (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
        ∀ t ∈ Icc 0 T, J.adjoint (U t) = J.adjoint u₀ +
          ∫ z in (0 : ℝ)..t, (M s v + F s) z - v z + J.adjoint (J (v z)) := by
  have hA : ContinuousAt (fun s => (formWeakHeatOperator J hc hd hi hn hT).comp (M s)) p :=
    continuousAt_const.clm_comp hM
  filter_upwards [hA.norm.eventually (gt_mem_nhds hsmall)] with s hs
  exact affineInitialValue_solution J hc hd hi hn hT (M s) hs (F s) u₀

end PoincareConjecture.M35.Uniqueness.Heat
