import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Local jets under a bounded linear readout

An actual equality of germs with a continuous linear postcomposition
transfers smoothness and every finite jet bound. Used for the intrinsic
comparison in Morgan-Tian Proposition 12.7, pp. 298-299; see
closed-time-cylinder-comparison.md.
-/

set_option autoImplicit false

open Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

/-- A bounded linear readout of a smooth germ preserves smoothness and
has the corresponding operator bound on its finite jets
(Proposition 12.7, pp. 298-299). -/
theorem clm_comp_germ_jet_bound
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (L : F →L[𝕜] G) {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt 𝕜 ∞ f x) (heq : g =ᶠ[𝓝 x] L ∘ f)
    (m : ℕ) {C A : ℝ} (hC : 0 ≤ C) (hL : ‖L‖ ≤ C)
    (hjet : ∀ j ≤ m, ‖iteratedFDeriv 𝕜 j f x‖ ≤ A) :
    ContDiffAt 𝕜 ∞ g x ∧ ∀ j ≤ m, ‖iteratedFDeriv 𝕜 j g x‖ ≤ C * A := by
  refine ⟨(L.contDiff.contDiffAt.comp x hf).congr_of_eventuallyEq heq, ?_⟩
  intro j hj
  rw [(heq.iteratedFDeriv 𝕜 j).self_of_nhds]
  exact (L.norm_iteratedFDeriv_comp_left hf (by exact_mod_cast le_top)).trans
    (mul_le_mul hL (hjet j hj) (norm_nonneg _) hC)

end Poincare.Analysis.Calculus
