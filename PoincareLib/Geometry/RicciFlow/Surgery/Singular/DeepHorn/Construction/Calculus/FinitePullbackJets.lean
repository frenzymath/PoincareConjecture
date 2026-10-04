import PoincareLib.Analysis.Calculus.SmoothCompactness.Operations

/-!
# Finite local jets for the fixed cylinder parametrization

Morgan--Tian Claim 11.35, printed p. 291, and Definition 2.16, p. 30.
These ordinary calculus estimates precede the included-time spatial
pullback. Reviewed derivation: claim11_35-strong-neck-transfer-calculus.md,
sections 1-2. M34/Mathlib/NeckLocalJetBounds is a read-only template;
the local derivative continuity comes directly from Mathlib.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology BigOperators
open Poincare.Analysis.Calculus

namespace PoincareMT.M32

/-- A smooth germ bounds its finite collection of ordinary jets on one
neighborhood. Claim 11.35, p. 291; transfer-calculus derivation, section 1. -/
theorem exists_eventually_finite_jet_bound
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {x : E} (hf : ContDiffAt 𝕜 ∞ f x) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ y in 𝓝 x, ∀ j ≤ N,
      ‖iteratedFDeriv 𝕜 j f y‖ ≤ C := by
  let B : Fin (N + 1) → ℝ := fun j => ‖iteratedFDeriv 𝕜 j f x‖ + 1
  have hB (j : Fin (N + 1)) : 0 ≤ B j := by dsimp [B]; positivity
  have hlocal (j : Fin (N + 1)) :
      ∀ᶠ y in 𝓝 x, ‖iteratedFDeriv 𝕜 j f y‖ ≤ B j := by
    have hc := (hf.continuousAt_iteratedFDeriv (k := j)
      (by exact_mod_cast le_top)).norm
    filter_upwards [hc.tendsto.eventually
      (isOpen_Iio.mem_nhds (lt_add_one ‖iteratedFDeriv 𝕜 j f x‖))] with y hy
    exact hy.le
  refine ⟨1 + ∑ j : Fin (N + 1), B j, ?_, ?_⟩
  · exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hB j)
  · have hall : ∀ᶠ y in 𝓝 x, ∀ j : Fin (N + 1),
        ‖iteratedFDeriv 𝕜 j f y‖ ≤ B j := eventually_all.mpr hlocal
    filter_upwards [hall] with y hy j hj
    let l : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    exact (hy l).trans ((Finset.single_le_sum
      (fun i _ => hB i) (Finset.mem_univ l)).trans (le_add_of_nonneg_left zero_le_one))

/-- One finite composition constant precedes both smooth germs and their
evaluation point. Claim 11.35, p. 291; transfer-calculus derivation, section 2. -/
theorem exists_composition_finite_jet_bound
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (N : ℕ) {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : E → F) (g : F → G) (x : E),
      ContDiffAt ℝ ∞ f x → ContDiffAt ℝ ∞ g (f x) →
      (∀ j ≤ N, ‖iteratedFDeriv ℝ j f x‖ ≤ B) →
      (∀ j ≤ N, ‖iteratedFDeriv ℝ j g (f x)‖ ≤ A) →
      ∀ j ≤ N, ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ C := by
  refine ⟨max 1 (N.factorial * A * B ^ N), le_max_left _ _, ?_⟩
  intro f g x hf hg hfj hgj j hj
  have h := norm_iteratedFDeriv_comp_le_of_contDiffAt hf hg j
    (fun l hl => hgj l (hl.trans hj))
    (fun l hl hlm => (hfj l (hlm.trans hj)).trans
      (le_self_pow₀ hB (Nat.ne_of_gt hl)))
  apply h.trans
  apply le_trans _ (le_max_right _ _)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj)
      (zero_le_one.trans hA))
    (pow_le_pow_right₀ hB hj) (pow_nonneg (zero_le_one.trans hB) _) (by positivity)

end PoincareMT.M32
