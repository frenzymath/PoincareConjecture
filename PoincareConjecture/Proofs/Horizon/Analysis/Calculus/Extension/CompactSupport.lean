import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Extension.Compact



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace Poincare.Analysis



theorem exists_contDiff_compactSupport_extension_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [NormedAddCommGroup F] [NormedSpace Real F]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : E -> F) (hf : ContDiffOn Real ∞ f U) :
    ∃ g : E -> F, ContDiff Real ∞ g ∧ HasCompactSupport g ∧ EqOn g f K := by
  obtain ⟨G, V, hG, _, hKV, _, heq⟩ :=
    exists_contDiff_extension_near_compact hK hU hKU f hf
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt 0 (0 : E)
  let χ : ContDiffBump (0 : E) := ⟨r, r + 1, hr, lt_add_one r⟩
  refine ⟨fun x => χ x • G x, χ.contDiff.smul hG, χ.hasCompactSupport.smul_right, ?_⟩
  intro x hx
  change χ x • G x = f x
  rw [χ.one_of_mem_closedBall (ball_subset_closedBall (hKr hx)), one_smul, heq (hKV hx)]

end Poincare.Analysis
