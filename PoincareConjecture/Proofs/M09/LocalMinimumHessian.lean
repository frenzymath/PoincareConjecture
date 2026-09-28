import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem localMin_secondDeriv_nonneg (f : ℝ → ℝ) (x : ℝ)
    (hf : ContinuousAt f x) (hmin : IsLocalMin f x) : 0 ≤ deriv (deriv f) x := by
  by_contra h
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge h
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hf
  have heq : f =ᶠ[𝓝 x] fun _ ↦ f x := by
    filter_upwards [hmin, hmax] with y hlow hupp
    exact le_antisymm hupp hlow
  have hdeq : deriv f =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [heq.deriv] with y hy
    simpa only [deriv_const] using hy
  have hzero : deriv (deriv f) x = 0 := by
    simpa only [deriv_const] using hdeq.deriv_eq
  exact hneg.ne hzero

theorem localMin_secondFDeriv_nonneg (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hmin : IsLocalMin f x) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let a : ℝ → E := fun t ↦ x + t • v
  have ha (t : ℝ) : HasDerivAt a v t := by
    simpa only [a, id_eq, one_smul] using ((hasDerivAt_id t).smul_const v).const_add x
  have ha0 : a 0 = x := by simp only [a, zero_smul, add_zero]
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    ((hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun y hy ↦ hy.differentiableAt (by simp))
  have hfirst : deriv (f ∘ a) =ᶠ[𝓝 (0 : ℝ)] fun t ↦ fderiv ℝ f (a t) v := by
    have hnear' : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ f (a t) :=
      ((ha 0).continuousAt.tendsto.mono_right (by rw [ha0])).eventually hnear
    filter_upwards [hnear'] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (ha t)).deriv
  have hD : DifferentiableAt ℝ (fderiv ℝ f) (a 0) := by
    rw [ha0]
    exact (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hsecond : HasDerivAt (fun t ↦ fderiv ℝ f (a t) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    simpa only [Function.comp_apply, ha0, map_zero, add_zero] using
      (hD.hasFDerivAt.comp_hasDerivAt 0 (ha 0)).clm_apply (hasDerivAt_const 0 v)
  have hmin' : IsLocalMin (f ∘ a) 0 := by
    have h := (ha 0).continuousAt.preimage_mem_nhds (show {y | f x ≤ f y} ∈ 𝓝 (a 0) from
      ha0.symm ▸ hmin)
    change ∀ᶠ t in 𝓝 (0 : ℝ), f (a 0) ≤ f (a t)
    rw [ha0]
    exact h
  have hf' : ContinuousAt (f ∘ a) 0 := by
    apply ContinuousAt.comp _ (ha 0).continuousAt
    simpa only [ha0] using hf.continuousAt
  have hpos := localMin_secondDeriv_nonneg (f ∘ a) 0 hf' hmin'
  rwa [hfirst.deriv_eq, hsecond.deriv] at hpos

theorem positiveSymmetricForm_zero_diagonal
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    (hpos : ∀ v, 0 ≤ B v v) (v : E) (hzero : B v v = 0) (w : E) : B v w = 0 := by
  let a : ℝ → E := fun t ↦ v + t • w
  have ha : HasDerivAt a w 0 := by
    simpa only [a, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hd : HasDerivAt (fun t ↦ B (a t) (a t)) (B w v + B v w) 0 := by
    simpa only [Function.comp_apply, a, zero_smul, add_zero] using
      (B.hasFDerivAt.comp_hasDerivAt 0 ha).clm_apply ha
  have hmin : IsLocalMin (fun t ↦ B (a t) (a t)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [a, zero_smul, add_zero, hzero] using hpos (a t)
  have hstat := hmin.hasDerivAt_eq_zero hd
  rw [hsymm w v] at hstat
  linarith

theorem localMin_secondFDeriv_zero_diagonal (f : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hmin : IsLocalMin f x)
    (v : E) (hv : fderiv ℝ (fderiv ℝ f) x v v = 0) (w : E) :
    fderiv ℝ (fderiv ℝ f) x v w = 0 := by
  have htwo : (2 : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  apply positiveSymmetricForm_zero_diagonal (fderiv ℝ (fderiv ℝ f) x)
    (fun v w ↦ hf.isSymmSndFDerivAt (by simpa using htwo) v w)
    (localMin_secondFDeriv_nonneg f x hf hmin) v hv w

end PoincareConjecture.Proofs.M09
