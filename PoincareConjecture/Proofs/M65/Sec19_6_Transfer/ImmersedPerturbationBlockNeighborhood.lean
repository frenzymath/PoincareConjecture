import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationDoublePoint
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

private theorem parameter_derivative_eq
    {P Z E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : P × Z → E) (w : P × Z) (hQ : DifferentiableAt ℝ Q w) :
    fderiv ℝ (fun p => Q (p, w.2)) w.1 =
      (fderiv ℝ Q w).comp ((ContinuousLinearMap.id ℝ P).prod (0 : P →L[ℝ] Z)) := by
  have hline := (hasFDerivAt_id (𝕜 := ℝ) w.1).prodMk (hasFDerivAt_const w.2 w.1)
  simpa +instances only [Function.comp_def, Prod.eta] using!
    (hQ.hasFDerivAt.comp w.1 hline).fderiv

private theorem exists_parameter_block_neighborhood
    {P Z E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : P × Z → E) (w : P × Z) (hQ : ContDiffAt ℝ 1 Q w)
    (hblock : Function.Bijective (fderiv ℝ (fun p => Q (p, w.2)) w.1)) :
    ∃ U : Set (P × Z), IsOpen U ∧ w ∈ U ∧ ContDiffOn ℝ 1 Q U ∧
      ∀ v ∈ U, Function.Bijective (fderiv ℝ (fun p => Q (p, v.2)) v.1) := by
  let B : P × Z → P →L[ℝ] E := fun v =>
    (fderiv ℝ Q v).comp ((ContinuousLinearMap.id ℝ P).prod (0 : P →L[ℝ] Z))
  have hB : ContinuousAt B w :=
    (hQ.continuousAt_fderiv one_ne_zero).clm_comp continuousAt_const
  have hBw : Function.Bijective (B w) := by
    change Function.Bijective ((fderiv ℝ Q w).comp
      ((ContinuousLinearMap.id ℝ P).prod (0 : P →L[ℝ] Z)))
    rw [← parameter_derivative_eq Q w hQ.differentiableAt_one]
    exact hblock
  let A : P ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective (B w)
    (LinearMap.ker_eq_bot.mpr hBw.1) (LinearMap.range_eq_top.mpr hBw.2)
  have hBrange : B w ∈ range ((↑) : (P ≃L[ℝ] E) → P →L[ℝ] E) :=
    ⟨A, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  have hnear := hB.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds hBrange)
  obtain ⟨O, hO, hQO⟩ := hQ.contDiffOn le_rfl (by simp)
  obtain ⟨U, hUsub, hU, hwU⟩ := mem_nhds_iff.mp (inter_mem hO hnear)
  have hQU : ContDiffOn ℝ 1 Q U := hQO.mono (fun _ hx => (hUsub hx).1)
  refine ⟨U, hU, hwU, hQU, ?_⟩
  intro v hv
  rw [parameter_derivative_eq Q v (hQU.contDiffAt (hU.mem_nhds hv)).differentiableAt_one]
  obtain ⟨e, he⟩ := (hUsub hv).2
  change Function.Bijective (B v)
  rw [← he]
  exact e.bijective

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {J : Set ℝ}

theorem exists_doublePoint_regular_neighborhood
    (C : M65SmoothFilledLoopFamily F J) (hJ : IsOpen J) (z : LoopAmbient) (ht : z 2 ∈ J)
    (hxy : (⟨Proofs.M58.angularPoint (z 0), Proofs.M58.norm_angularPoint (z 0)⟩ : LoopCircle) ≠
      ⟨Proofs.M58.angularPoint (z 1), Proofs.M58.norm_angularPoint (z 1)⟩)
    (heq : periodicFreeLoop (C.loops (z 2)) (z 0) = periodicFreeLoop (C.loops (z 2)) (z 1)) :
    ∃ (d : ℝ) (beta : LoopPlane → ℝ) (Phi : Fin 3 → M × ℝ → M)
        (U : Set ((Fin 3 → ℝ) × LoopAmbient)),
      0 < d ∧ ContDiff ℝ ∞ beta ∧ (∀ w, beta w ∈ Icc (0 : ℝ) 1) ∧
      beta (Proofs.M58.angularPoint (z 0)) = 1 ∧
      beta (Proofs.M58.angularPoint (z 1)) = 0 ∧
      (∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
        (univ ×ˢ Ioo (-d) d)) ∧ (∀ i y, Phi i (y, 0) = y) ∧
      IsOpen U ∧ (0, z) ∈ U ∧
      ContDiffOn ℝ 1 (doublePointEquation C Phi
        (fun _ x => beta (Proofs.M58.angularPoint x)) (List.finRange 3)
        (periodicFreeLoop (C.loops (z 2)) (z 0))) U ∧
      ∀ w ∈ U, Function.Bijective (fderiv ℝ (fun p =>
        doublePointEquation C Phi (fun _ x => beta (Proofs.M58.angularPoint x))
          (List.finRange 3) (periodicFreeLoop (C.loops (z 2)) (z 0)) (p, w.2)) w.1) := by
  obtain ⟨d, beta, Phi, hd, hbeta, hbound, hx, hy, hPhi, hzero, hblock⟩ :=
    exists_doublePoint_regular_controls C z hxy heq
  obtain ⟨hweight, _, hweightBound⟩ := source_weight_regular beta hbeta hbound
  have hxq : periodicFreeLoop (C.loops (z 2)) (z 0) ∈
      (chartAt LoopAmbient (periodicFreeLoop (C.loops (z 2)) (z 0))).source :=
    mem_chart_source _ _
  have hyq : periodicFreeLoop (C.loops (z 2)) (z 1) ∈
      (chartAt LoopAmbient (periodicFreeLoop (C.loops (z 2)) (z 0))).source := heq ▸ hxq
  have hQ := doublePointEquation_contDiffAt C hJ Phi
    (fun _ x => beta (Proofs.M58.angularPoint x)) d hd hPhi hzero
    (fun _ => hweight) (fun _ => hweightBound) (List.finRange 3)
    (periodicFreeLoop (C.loops (z 2)) (z 0)) z ht hxq hyq
  obtain ⟨U, hU, hwU, hQU, hBU⟩ := exists_parameter_block_neighborhood _ (0, z)
    (hQ.of_le (by simp)) hblock
  exact ⟨d, beta, Phi, U, hd, hbeta, hbound, hx, hy, hPhi, hzero, hU, hwU, hQU, hBU⟩

end PoincareConjecture.M65Perturbation
