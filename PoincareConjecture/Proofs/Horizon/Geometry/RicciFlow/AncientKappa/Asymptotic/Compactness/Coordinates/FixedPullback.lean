import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.SpacetimePullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

theorem tendstoUniformlyOn_constant_jets
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (r : ℕ) (K : Set X) :
    TendstoUniformlyOn (fun _ : ℕ => iteratedFDeriv ℝ r f) (iteratedFDeriv ℝ r f) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε

theorem smooth_convergence_fixed_spacetime_bilinear_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J : Set ℝ} {U V : Set E} (hJ : IsOpen J) (hU : IsOpen U) (hV : IsOpen V)
    {a : E → E} (ha : ContDiffOn ℝ ∞ a U) (hUV : MapsTo a U V)
    {B : ℕ → ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {B₀ : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB₀ : ContDiffOn ℝ ∞ B₀ (J ×ˢ V))
    (hBlocal : ∀ z ∈ J ×ˢ V, ∃ W, IsOpen W ∧ z ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (B k) W)
    (hBjet : ∀ m K, IsCompact K → K ⊆ J ×ˢ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (B k)) (iteratedFDeriv ℝ m B₀) atTop K) :
    ∀ m K, IsCompact K → K ⊆ J ×ˢ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun z : ℝ × E =>
        (B k (z.1, a z.2)).bilinearComp (fderiv ℝ a z.2) (fderiv ℝ a z.2)))
      (iteratedFDeriv ℝ m (fun z : ℝ × E =>
        (B₀ (z.1, a z.2)).bilinearComp (fderiv ℝ a z.2) (fderiv ℝ a z.2))) atTop K := by
  let T := E →L[ℝ] E →L[ℝ] ℝ
  let : NormedAddCommGroup T := inferInstance
  let : NormedSpace ℝ T := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let lift : ℝ × E → ℝ × E := fun z => (z.1, a z.2)
  let deriv : ℝ × E → E →L[ℝ] E := fun z => fderiv ℝ a z.2
  have hlift : ContDiffOn ℝ ∞ lift (J ×ˢ U) :=
    contDiff_fst.contDiffOn.prodMk (ha.comp contDiff_snd.contDiffOn (fun _ hz => hz.2))
  have hderiv : ContDiffOn ℝ ∞ deriv (J ×ˢ U) :=
    (ha.fderiv_of_isOpen hU (by simp)).comp contDiff_snd.contDiffOn (fun _ hz => hz.2)
  obtain ⟨hClocal, hCjet⟩ := smooth_convergence_comp_on_finiteDimensional
    (hJ.prod hV) (hJ.prod hU) hB₀ hlift (fun z hz => ⟨hz.1, hUV hz.2⟩) hBlocal
    (fun z hz => ⟨J ×ˢ U, hJ.prod hU, hz, Eventually.of_forall fun _ => hlift⟩)
    hBjet (fun m K _ _ => tendstoUniformlyOn_constant_jets lift m K)
  have hC₀ : ContDiffOn ℝ ∞ (B₀ ∘ lift) (J ×ˢ U) :=
    hB₀.comp hlift (fun z hz => ⟨hz.1, hUV hz.2⟩)
  let flip : T →L[ℝ] T :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let op : T →L[ℝ] (E →L[ℝ] E) →L[ℝ] T :=
    (ContinuousLinearMap.compL ℝ (E →L[ℝ] E) T T flip).comp
      (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ))
  have hop (b : T) (A : E →L[ℝ] E) : op b A = (b.comp A).flip := rfl
  have hdlocal : ∀ z ∈ J ×ˢ U, ∃ W, IsOpen W ∧ z ∈ W ∧
      ∀ᶠ k : ℕ in atTop, ContDiffOn ℝ ∞ deriv W :=
    fun z hz => ⟨J ×ˢ U, hJ.prod hU, hz, Eventually.of_forall fun _ => hderiv⟩
  obtain ⟨hfirstlocal, hfirstjet⟩ := smooth_convergence_bilinear_on_finiteDimensional
    (hJ.prod hU) op hC₀ hderiv
    (fun z hz => let ⟨W, hW, hzW, _, hks⟩ := hClocal z hz; ⟨W, hW, hzW, hks⟩)
    hdlocal hCjet (fun m K _ _ => tendstoUniformlyOn_constant_jets deriv m K)
  have hfirst₀ : ContDiffOn ℝ ∞ (fun z => op (B₀ (lift z)) (deriv z)) (J ×ˢ U) :=
    op.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hC₀ hderiv
  have hsecond := smooth_convergence_bilinear_on_finiteDimensional (hJ.prod hU) op
    hfirst₀ hderiv
    (fun z hz => let ⟨W, hW, hzW, _, hks⟩ := hfirstlocal z hz; ⟨W, hW, hzW, hks⟩)
    hdlocal hfirstjet (fun m K _ _ => tendstoUniformlyOn_constant_jets deriv m K)
  simpa only [hop, Function.comp_apply, ContinuousLinearMap.bilinearComp,
    lift, deriv] using hsecond.2

end Poincare.Analysis.Calculus
