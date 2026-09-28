import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false

open Set MeasureTheory

namespace MeasureTheory

variable {X E : Type*} [MeasurableSpace X] {mu : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem MemLp.norm_toLp_sq {f : X → E} (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂mu := by
  rw [Lp.norm_sq_eq_integral_norm_sq]
  exact integral_congr_ae (hf.coeFn_toLp.mono fun _ hx =>
    congrArg (fun v : E => ‖v‖ ^ 2) hx)

theorem LpToLpRestrictCLM_toLp {f : X → E} (hf : MemLp f 2 mu) (S : Set X) :
    LpToLpRestrictCLM X E ℝ mu 2 S (hf.toLp f) = (hf.restrict S).toLp f := by
  apply Lp.ext
  have hae : (hf.toLp f : X → E) =ᵐ[mu.restrict S] f :=
    ae_restrict_of_ae hf.coeFn_toLp
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ S (hf.toLp f), hae,
    (hf.restrict S).coeFn_toLp] with x h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

omit [InnerProductSpace ℝ E] in

theorem MemLp.norm_toLp_restrict_eq_of_zero {f : X → E} (hf : MemLp f 2 mu)
    {S : Set X} (hS : MeasurableSet S) (hzero : ∀ x, x ∉ S → f x = 0) :
    ‖(hf.restrict S).toLp f‖ = ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp, ← eLpNorm_indicator_eq_eLpNorm_restrict hS]
  congr 2
  funext x
  by_cases hx : x ∈ S
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, hzero x hx]

end MeasureTheory
