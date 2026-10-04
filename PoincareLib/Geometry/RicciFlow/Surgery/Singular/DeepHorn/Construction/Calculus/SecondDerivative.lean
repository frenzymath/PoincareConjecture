import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Second derivative of a smooth composition

The twice differentiated chain rule is the finite-calculus step behind
the scalar Laplacian in Morgan--Tian equation (3.7), printed p. 41, and
the signed scalar estimate in Claim 11.35, pp. 289-291.

Locally re-derived from the read-only M44 Mathlib/SecondDerivativeComposition
declaration `second_fderiv_comp_of_contDiffAt`. No later proof is imported.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace PoincareMT.M32

/-- The second chain rule at smooth germs, with the derivative direction
in the first slot; equation (3.7), p. 41, as used in Claim 11.35, p. 289. -/
theorem second_fderiv_comp_of_contDiffAt
    {E J F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → J} {g : J → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) (u v : E) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) x u v =
      fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) +
        fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x u v) := by
  have hf' := hf.fderiv_right (m := ∞) (by simp)
  have hg' := hg.fderiv_right (m := ∞) (by simp)
  have hchain := ((hg'.differentiableAt (by simp)).hasFDerivAt.comp x
    (hf.differentiableAt (by simp)).hasFDerivAt).clm_apply
      ((hf'.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have hcomp : ContDiffAt ℝ ∞ (g ∘ f) x := hg.comp x hf
  have heval := ((hcomp.fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have heq : (fun y => fderiv ℝ (g ∘ f) y v) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ g (f y) (fderiv ℝ f y v)) := by
    have hfe := (hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
    have hge := (hg.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
    filter_upwards [hfe, hf.continuousAt.eventually hge] with y hfy hgy
    rw [fderiv_comp y (hgy.differentiableAt (by simp)) (hfy.differentiableAt (by simp))]
    rfl
  have h := congrArg (fun A => A u)
    (heval.fderiv.symm.trans (heq.fderiv_eq.trans hchain.fderiv))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    Function.comp_apply, add_apply, zero_apply, map_zero, zero_add, add_zero, add_comm]
    using h

/-- Continuity of the second chain-rule contraction with arbitrary
continuous parameter maps. This is the finite calculus in equation (3.7),
p. 41, used in Claim 11.35, p. 289; re-derived from the read-only M44
`continuousAt_secondDerivativeContractionReadout`. -/
theorem continuousAt_secondDerivativeContraction
    {E J X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup J] [NormedSpace ℝ J] [TopologicalSpace X] [Fintype ι]
    {g : J → ℝ} (e : ι → E) {a : X → J} {b : X → E →L[ℝ] J}
    {d : X → E →L[ℝ] E →L[ℝ] J} {v : ι → X → E} {c : X → E} {x : X}
    (hg : ContDiffAt ℝ ∞ g (a x)) (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hd : ContinuousAt d x) (hv : ∀ i, ContinuousAt (v i) x) (hc : ContinuousAt c x) :
    ContinuousAt (fun y =>
      (∑ i, (fderiv ℝ (fderiv ℝ g) (a y) (b y (e i)) (b y (v i y)) +
        fderiv ℝ g (a y) (d y (e i) (v i y)))) -
      fderiv ℝ g (a y) (b y (c y))) x := by
  have hg' := hg.fderiv_right (m := ∞) (by simp)
  have hg'' := hg'.fderiv_right (m := ∞) (by simp)
  have hfirst := hg'.continuousAt.comp ha
  have hsecond := hg''.continuousAt.comp ha
  apply ContinuousAt.sub
  · apply tendsto_finsetSum
    intro i _
    exact ((hsecond.clm_apply (hb.clm_apply continuousAt_const)).clm_apply
      (hb.clm_apply (hv i))).add
        (hfirst.clm_apply ((hd.clm_apply continuousAt_const).clm_apply (hv i)))
  · exact hfirst.clm_apply (hb.clm_apply hc)

/-- Subtraction commutes with the full triple of a smooth function and
its first two derivatives. This is the norm-difference calculus behind
equation (3.7), p. 41, and Claim 11.35, printed p. 289. -/
theorem secondDerivativeTriple_sub
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B C : E → F} (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C) (x : E) :
    ((B - C) x, fderiv ℝ (B - C) x, fderiv ℝ (fderiv ℝ (B - C)) x) =
      (B x, fderiv ℝ B x, fderiv ℝ (fderiv ℝ B) x) -
        (C x, fderiv ℝ C x, fderiv ℝ (fderiv ℝ C) x) := by
  have hB' := hB.fderiv_right (m := ∞) (by simp)
  have hC' := hC.fderiv_right (m := ∞) (by simp)
  have hfirst : fderiv ℝ (B - C) = fderiv ℝ B - fderiv ℝ C := by
    funext y
    exact fderiv_sub (hB.differentiable (by simp) y) (hC.differentiable (by simp) y)
  have hsecond : fderiv ℝ (fderiv ℝ (B - C)) =
      fderiv ℝ (fderiv ℝ B) - fderiv ℝ (fderiv ℝ C) := by
    rw [hfirst]
    funext y
    exact fderiv_sub (hB'.differentiable (by simp) y) (hC'.differentiable (by simp) y)
  rw [hsecond, hfirst]
  rfl

end PoincareMT.M32
