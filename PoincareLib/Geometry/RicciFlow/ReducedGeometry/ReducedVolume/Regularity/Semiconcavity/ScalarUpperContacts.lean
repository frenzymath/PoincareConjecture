import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

/-!
# The strict upper-contact minimum principle

Morgan-Tian Claim 7.18, with the concavity correction for Corollary 7.19.
A continuous upper contact with negative second derivative excludes a local
minimum. Compact minimization then bounds a continuous interval function
below by the smaller endpoint value. No differentiability of that function
is required.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareMT.ReducedVolume

/-- A negative-second-derivative upper contact is incompatible with a local minimum. -/
theorem not_isLocalMin_of_strict_upper_contact {f B : ℝ → ℝ} {c : ℝ}
    (hcontact : B c = f c) (hupper : ∀ᶠ t in 𝓝 c, f t ≤ B t)
    (hcont : ContinuousAt B c) (hsecond : deriv (deriv B) c < 0) :
    ¬ IsLocalMin f c := by
  intro hmin
  have hBmin : IsLocalMin B c := by
    filter_upwards [hmin, hupper] with t ht htB
    exact hcontact.trans_le (ht.trans htB)
  have hBmax := isLocalMax_of_deriv_deriv_neg hsecond hBmin.deriv_eq_zero hcont
  have heq : B =ᶠ[𝓝 c] (fun _ ↦ B c) := by
    filter_upwards [hBmin, hBmax] with t ht₁ ht₂
    exact le_antisymm ht₂ ht₁
  have hzero : deriv (deriv B) c = 0 := by
    simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
  linarith only [hsecond, hzero]

/-- Strictly concave upper contacts force the endpoint minimum bound on a compact interval. -/
theorem min_endpoints_le_of_strict_upper_contacts {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hcontacts : ∀ c ∈ Ioo a b, ∃ B : ℝ → ℝ,
      B c = f c ∧ (∀ᶠ t in 𝓝 c, f t ≤ B t) ∧
        ContinuousAt B c ∧ deriv (deriv B) c < 0)
    {x : ℝ} (hx : x ∈ Icc a b) : min (f a) (f b) ≤ f x := by
  by_contra! hbad
  obtain ⟨c, hc, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hf
  have hcx : f c ≤ f x := hmin hx
  have hca : c ≠ a := by
    intro heq
    subst c
    exact (not_lt_of_ge (hcx.trans' (min_le_left _ _))) hbad
  have hcb : c ≠ b := by
    intro heq
    subst c
    exact (not_lt_of_ge (hcx.trans' (min_le_right _ _))) hbad
  have hcint : c ∈ Ioo a b := ⟨lt_of_le_of_ne hc.1 hca.symm, lt_of_le_of_ne hc.2 hcb⟩
  obtain ⟨B, hcontact, hupper, hcont, hsecond⟩ := hcontacts c hcint
  exact not_isLocalMin_of_strict_upper_contact hcontact hupper hcont hsecond
    (hmin.isLocalMin (Icc_mem_nhds hcint.1 hcint.2))

end PoincareMT.ReducedVolume
