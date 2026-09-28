import PoincareConjecture.Proofs.M47.TerminalGermsClosedJets
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology NNReal

namespace PoincareConjecture.M47




theorem terminalGerms_contDiffOn_closure_of_bounded_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) (hconvex : Convex ℝ U)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f U)
    (hcontinuous : ContinuousOn f (closure U))
    (hbound : ∀ m : ℕ, ∃ C : ℝ≥0,
      ∀ x ∈ U, ‖iteratedFDeriv ℝ (m + 1) f x‖ ≤ C) :
    ContDiffOn ℝ ∞ f (closure U) := by
  classical
  have : ∀ m : ℕ, FiniteDimensional ℝ (E [×m]→L[ℝ] F) := by
    intro m
    induction m with
    | zero => exact (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearEquiv.finiteDimensional
    | succ m ih => exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => E) F).symm.toLinearEquiv.finiteDimensional
  have hdiff (m : ℕ) (x : E) (hx : x ∈ U) :
      DifferentiableAt ℝ (iteratedFDeriv ℝ m f) x :=
    (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop (N := (∞ : ℕ∞ω)) le_rfl m)
  choose C hC using hbound
  have hlip (m : ℕ) : LipschitzOnWith (C m) (iteratedFDeriv ℝ m f) U := by
    apply hconvex.lipschitzOnWith_of_nnnorm_fderiv_le (hdiff m)
    intro x hx
    change ‖fderiv ℝ (iteratedFDeriv ℝ m f) x‖ ≤ (C m : ℝ)
    rw [norm_fderiv_iteratedFDeriv]
    exact hC m x hx
  choose P hPlip hPeq using fun m => (hlip m).extend_finite_dimension
  have hPcontinuous (m : ℕ) : Continuous (P m) := (hPlip m).continuous
  let fext : E → F := fun x => (P 0 x).curry0
  have hfext : Continuous fext :=
    (continuousMultilinearCurryFin0 ℝ E F).continuous.comp (hPcontinuous 0)
  have hzeroU : EqOn fext f U := by
    intro x hx
    change (P 0 x).curry0 = f x
    rw [← hPeq 0 hx]
    rfl
  have hzero := hzeroU.of_subset_closure hfext.continuousOn hcontinuous
    subset_closure subset_rfl
  apply (terminalGerms_closed_taylor_jets hU hconvex f (fun x m => P m x)
    hzero (fun m => (hPcontinuous m).continuousOn) ?_).2
  intro m x hx
  have hlocal : P m =ᶠ[𝓝 x] iteratedFDeriv ℝ m f := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hPeq m hy).symm
  rw [← hPeq (m + 1) hx]
  have hd := (hdiff m x hx).hasFDerivAt.congr_of_eventuallyEq hlocal
  simpa only [iteratedFDeriv, ContinuousLinearMap.curry_uncurryLeft] using hd



theorem terminalGerms_contDiffOn_closure_of_source_bounds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) (hconvex : Convex ℝ U)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f U)
    (hcontinuous : ContinuousOn f (closure U))
    (source : ℕ → E → F)
    (hjets : ∀ m : ℕ, ∀ x ∈ U,
      Tendsto (fun k => iteratedFDeriv ℝ (m + 1) (source k) x) atTop
        (𝓝 (iteratedFDeriv ℝ (m + 1) f x)))
    (hbound : ∀ m : ℕ, ∃ C : ℝ≥0, ∀ᶠ k in atTop,
      ∀ x ∈ U, ‖iteratedFDeriv ℝ (m + 1) (source k) x‖ ≤ C) :
    ContDiffOn ℝ ∞ f (closure U) := by
  apply terminalGerms_contDiffOn_closure_of_bounded_jets hU hconvex f hf hcontinuous
  intro m
  obtain ⟨C, hC⟩ := hbound m
  refine ⟨C, fun x hx => ?_⟩
  exact le_of_tendsto (hjets m x hx).norm (hC.mono fun k hk => hk x hx)

end PoincareConjecture.M47
