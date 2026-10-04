import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smoothness of an actual autonomous ODE solution germ

A smooth vector field and actual derivative witnesses on a neighborhood
give all finite orders of regularity by the successor derivative criterion.
This is the scalar-time bootstrap used for the geodesic sides in MT2007
Definition 19.18, p. 450; see `2026-09-21-geodesic-smoothness.md`.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

/-- A solution germ of a smooth autonomous ODE is smooth. Derivative
witnesses on a neighborhood supply the local order-zero continuity as
well as the induction step. Used for MT2007 Definition 19.18, p. 450. -/
theorem contDiffAt_infty_of_hasDerivAt_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {V : E → E} {t : ℝ}
    (hV : ContDiffAt ℝ ∞ V (f t))
    (hf : ∀ᶠ s in 𝓝 t, HasDerivAt f (V (f s)) s) :
    ContDiffAt ℝ ∞ f t := by
  apply contDiffAt_infty.mpr
  intro k
  induction k with
  | zero =>
      exact contDiffAt_zero.mpr ⟨{s | HasDerivAt f (V (f s)) s}, hf,
        fun _ hs => hs.continuousAt.continuousWithinAt⟩
  | succ k ih =>
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨fun s => ContinuousLinearMap.toSpanSingleton ℝ (V (f s)),
        ⟨{s | HasDerivAt f (V (f s)) s}, hf, fun _ hs => hs.hasFDerivAt⟩, ?_⟩
      have hVk : ContDiffAt ℝ k V (f t) :=
        hV.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
      exact (ContinuousLinearMap.toSpanSingletonLIE ℝ E).contDiff.contDiffAt.comp t
        (hVk.comp t ih)
