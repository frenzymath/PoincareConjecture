import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Pullback







set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

theorem smooth_convergence_sub_limit
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {f : ℕ → E → F} {f₀ : E → F}
    (hf₀ : ContDiffOn ℝ ∞ f₀ U)
    (hlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (f i) W)
    (hjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (f i)) (iteratedFDeriv ℝ m f₀) atTop K) :
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (fun y => f i y - f₀ y) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (fun y => f i y - f₀ y)) (fun _ => 0) atTop K := by
  constructor
  · intro x hx
    obtain ⟨W, hW, hxW, hi⟩ := hlocal x hx
    refine ⟨U ∩ W, hU.inter hW, ⟨hx, hxW⟩, ?_⟩
    exact hi.mono fun i h => (h.mono inter_subset_right).sub (hf₀.mono inter_subset_left)
  · intro m K hK hKU
    have hc : TendstoUniformlyOn (fun _ : ℕ => iteratedFDeriv ℝ m f₀)
        (iteratedFDeriv ℝ m f₀) atTop K := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      exact Eventually.of_forall fun _ _ _ => by simpa using hε
    have h := (hjet m K hK hKU).sub hc
    apply (h.congr ?_).congr_right ?_
    · filter_upwards [eventually_contDiffAt_on_compact hK hKU hlocal] with i hi x hx
      exact (iteratedFDeriv_sub_apply
        ((hi x hx).of_le (by exact_mod_cast le_top))
        ((hf₀.contDiffAt (hU.mem_nhds (hKU hx))).of_le
          (by exact_mod_cast le_top))).symm
    · intro x hx
      simp

end Poincare.Analysis.Calculus
