import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Pullback









set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]


theorem locally_eventually_smooth_continuousLinearMap_comp
    (L : F →L[ℝ] G) {U : Set E} {f : ℕ → E → F}
    (hlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W) :
    ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (L ∘ f k) W := by
  intro x hx
  obtain ⟨W, hW, hxW, hks⟩ := hlocal x hx
  exact ⟨W, hW, hxW, hks.mono fun _ hk => hk.continuousLinearMap_comp L⟩



theorem smooth_convergence_continuousLinearMap_comp
    (L : F →L[ℝ] G) {U : Set E} (hU : IsOpen U)
    {f : ℕ → E → F} {f₀ : E → F} (hf₀ : ContDiffOn ℝ ∞ f₀ U)
    (hlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m f₀) atTop K) :
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (L ∘ f k) W) ∧
      ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (L ∘ f k))
        (iteratedFDeriv ℝ m (L ∘ f₀)) atTop K := by
  refine ⟨locally_eventually_smooth_continuousLinearMap_comp L hlocal, ?_⟩
  intro m K hK hKU
  have h := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin m => E) F G L).uniformContinuous.comp_tendstoUniformlyOn
      (hjet m K hK hKU)
  apply (h.congr ?_).congr_right ?_
  · filter_upwards [eventually_contDiffAt_on_compact hK hKU hlocal] with k hk x hx
    exact (L.iteratedFDeriv_comp_left (hk x hx) (by exact_mod_cast le_top)).symm
  · intro x hx
    exact (L.iteratedFDeriv_comp_left (hf₀.contDiffAt (hU.mem_nhds (hKU hx)))
      (by exact_mod_cast le_top)).symm

end Poincare.Analysis.Calculus
