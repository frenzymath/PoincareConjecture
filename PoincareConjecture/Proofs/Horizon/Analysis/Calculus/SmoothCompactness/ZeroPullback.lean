import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.ZeroComposition
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.ZeroBilinear








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

theorem smooth_zero_convergence_pullback_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U V : Set E} (hV : IsOpen V)
    {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {a : ℕ → E → E}
    (hBlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (B k) W)
    (halocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k) W)
    (hBjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (B k)) (fun _ => 0) atTop K)
    (habound : ∀ K, IsCompact K → K ⊆ V → ∀ m, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (a k) x‖ ≤ C)
    (hatarget : ∀ K, IsCompact K → K ⊆ V → ∃ T,
      IsCompact T ∧ T ⊆ U ∧ ∀ᶠ k in atTop, MapsTo (a k) K T) :
    (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fun y => (B k (a k y)).bilinearComp
        (fderiv ℝ (a k) y) (fderiv ℝ (a k) y)) W) ∧
      ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (fun y => (B k (a k y)).bilinearComp
          (fderiv ℝ (a k) y) (fderiv ℝ (a k) y)))
        (fun _ => 0) atTop K := by
  let T := E →L[ℝ] E →L[ℝ] ℝ
  let : NormedAddCommGroup T := inferInstance
  let : NormedSpace ℝ T := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let flip : T →L[ℝ] T :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let op : T →L[ℝ] (E →L[ℝ] E) →L[ℝ] T :=
    (ContinuousLinearMap.compL ℝ (E →L[ℝ] E) T T flip).comp
      (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ))
  have hop (b : T) (A : E →L[ℝ] E) : op b A = (b.comp A).flip := rfl
  obtain ⟨hClocal, hCjet⟩ := smooth_zero_convergence_comp_of_bounded hV
    hBlocal halocal (fun m K hK hKU => (hBjet m K hK hKU).congr_right (fun _ _ => by simp))
    habound hatarget
  have hdlocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fderiv ℝ (a k)) W := by
    intro x hx
    obtain ⟨W, hW, hxW, hks⟩ := halocal x hx
    exact ⟨W, hW, hxW, hks.mono fun k hk => hk.fderiv_of_isOpen hW (by simp)⟩
  have hdbound : ∀ K, IsCompact K → K ⊆ V → ∀ m, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (fderiv ℝ (a k)) x‖ ≤ C := by
    intro K hK hKV m
    simpa only [norm_iteratedFDeriv_fderiv] using habound K hK hKV (m + 1)
  obtain ⟨hfirstlocal, hfirstjet⟩ := smooth_convergence_zero_bilinear_on_open hV op
    (fun x hx => let ⟨W, hW, hxW, _, hks⟩ := hClocal x hx; ⟨W, hW, hxW, hks⟩)
    hdlocal (fun m K hK hKV => (hCjet m K hK hKV).congr_right (fun _ _ => by simp)) hdbound
  have hsecond := smooth_convergence_zero_bilinear_on_open hV op
    (fun x hx => let ⟨W, hW, hxW, _, hks⟩ := hfirstlocal x hx; ⟨W, hW, hxW, hks⟩)
    hdlocal hfirstjet hdbound
  simpa only [hop, Function.comp_apply, ContinuousLinearMap.bilinearComp] using hsecond

end Poincare.Analysis.Calculus
