import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.DomainChange
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LinearPrecompose











set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem smooth_convergence_spacetime_lift
    {U : Set E} (hU : IsOpen U) {a : ℕ → E → E}
    (halocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k) W)
    (hajet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m id) atTop K) :
    (∀ z ∈ (Prod.snd : ℝ × E → E) ⁻¹' U, ∃ W, IsOpen W ∧ z ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fun y : ℝ × E => (y.1, a k y.2)) W) ∧
      ∀ m K, IsCompact K → K ⊆ (Prod.snd : ℝ × E → E) ⁻¹' U → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (fun y : ℝ × E => (y.1, a k y.2)))
        (iteratedFDeriv ℝ m id) atTop K := by
  obtain ⟨hsndlocal, hsndjet⟩ := smooth_convergence_comp_continuousLinearMap
    (ContinuousLinearMap.snd ℝ ℝ E) hU contDiff_id.contDiffOn halocal hajet
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨W, hW, hzW, hks⟩ := hsndlocal z hz
    exact ⟨W, hW, hzW, hks.mono fun k hk => contDiff_fst.contDiffOn.prodMk hk⟩
  · intro m K hK hKU
    have hpair : TendstoUniformlyOn
        (fun k z => (iteratedFDeriv ℝ m (Prod.fst : ℝ × E → ℝ) z,
          iteratedFDeriv ℝ m (fun y : ℝ × E => a k y.2) z))
        (fun z => (iteratedFDeriv ℝ m (Prod.fst : ℝ × E → ℝ) z,
          iteratedFDeriv ℝ m (Prod.snd : ℝ × E → E) z)) atTop K := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hsndjet m K hK hKU) ε hε]
        with k hk z hz
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
        Function.comp_def, id_eq, ContinuousLinearMap.coe_snd'] using hk z hz
    let prod := ContinuousMultilinearMap.prodL ℝ (fun _ : Fin m => ℝ × E) ℝ E
    have hprod := prod.isometry.uniformContinuous.comp_tendstoUniformlyOn hpair
    apply (hprod.congr ?_).congr_right ?_
    · filter_upwards [eventually_contDiffAt_on_compact hK hKU hsndlocal]
        with k hk z hz
      exact (iteratedFDeriv_prodMk contDiffAt_fst (hk z hz)
        (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)).symm
    · intro z _
      exact (iteratedFDeriv_prodMk contDiffAt_fst
        (contDiffAt_snd : ContDiffAt ℝ ∞ (Prod.snd : ℝ × E → E) z)
        (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)).symm




theorem smooth_convergence_spacetime_bilinear_pullback
    [FiniteDimensional ℝ E]
    {J : Set ℝ} {U : Set E} (hJ : IsOpen J) (hU : IsOpen U)
    {a : ℕ → E → E}
    {B : ℕ → ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {B₀ : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB₀ : ContDiffOn ℝ ∞ B₀ (J ×ˢ U))
    (halocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k) W)
    (hBlocal : ∀ z ∈ J ×ˢ U, ∃ W, IsOpen W ∧ z ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (B k) W)
    (hajet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m id) atTop K)
    (hBjet : ∀ m K, IsCompact K → K ⊆ J ×ˢ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (B k)) (iteratedFDeriv ℝ m B₀) atTop K) :
    (∀ z ∈ J ×ˢ U, ∃ W, IsOpen W ∧ z ∈ W ∧ W ⊆ J ×ˢ U ∧ ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ (fun y : ℝ × E => (B k (y.1, a k y.2)).bilinearComp
        (fderiv ℝ (a k) y.2) (fderiv ℝ (a k) y.2)) W) ∧
      ∀ m K, IsCompact K → K ⊆ J ×ˢ U → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (fun y : ℝ × E => (B k (y.1, a k y.2)).bilinearComp
          (fderiv ℝ (a k) y.2) (fderiv ℝ (a k) y.2)))
        (iteratedFDeriv ℝ m B₀) atTop K := by
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
  have hJU := hJ.prod hU
  obtain ⟨hliftlocal, hliftjet⟩ := smooth_convergence_spacetime_lift hU halocal hajet
  obtain ⟨hClocal, hCjet⟩ := smooth_convergence_comp_on_finiteDimensional hJU hJU
    hB₀ contDiff_id.contDiffOn (fun _ hz => hz) hBlocal
    (fun z hz => hliftlocal z hz.2)
    (hBjet) (fun m K hK hKU => hliftjet m K hK (fun z hz => (hKU hz).2))
  have hdlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fderiv ℝ (a k)) W := by
    intro x hx
    obtain ⟨W, hW, hxW, hks⟩ := halocal x hx
    exact ⟨W, hW, hxW, hks.mono fun k hk => hk.fderiv_of_isOpen hW (by simp)⟩
  have hdjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fderiv ℝ (a k)))
      (iteratedFDeriv ℝ m (fun _ : E => ContinuousLinearMap.id ℝ E)) atTop K := by
    intro m K hK hKU
    have hid : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
      funext fun x => fderiv_id
    simpa only [hid] using tendstoUniformlyOn_fderiv_jets m (hajet (m + 1) K hK hKU)
  obtain ⟨hdliftlocal, hdliftjet⟩ := smooth_convergence_comp_continuousLinearMap
    (ContinuousLinearMap.snd ℝ ℝ E) hU contDiff_const.contDiffOn hdlocal hdjet
  have hdliftlocal' : ∀ z ∈ J ×ˢ U, ∃ W, IsOpen W ∧ z ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fun y : ℝ × E => fderiv ℝ (a k) y.2) W :=
    fun z hz => hdliftlocal z hz.2
  have hdliftjet' : ∀ m K, IsCompact K → K ⊆ J ×ˢ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun y : ℝ × E => fderiv ℝ (a k) y.2))
      (iteratedFDeriv ℝ m (fun _ : ℝ × E => ContinuousLinearMap.id ℝ E)) atTop K :=
    fun m K hK hKU => hdliftjet m K hK (fun z hz => (hKU hz).2)
  obtain ⟨hfirstlocal, hfirstjet⟩ := smooth_convergence_bilinear_on_finiteDimensional hJU op
    hB₀ contDiff_const.contDiffOn
    (fun z hz => let ⟨W, hW, hzW, _, hks⟩ := hClocal z hz; ⟨W, hW, hzW, hks⟩)
    hdliftlocal' hCjet hdliftjet'
  have hfirst₀ : ContDiffOn ℝ ∞ (fun y => op (B₀ y) (ContinuousLinearMap.id ℝ E)) (J ×ˢ U) :=
    op.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hB₀ contDiff_const.contDiffOn
  have hsecond := smooth_convergence_bilinear_on_finiteDimensional hJU op hfirst₀
    contDiff_const.contDiffOn
    (fun z hz => let ⟨W, hW, hzW, _, hks⟩ := hfirstlocal z hz; ⟨W, hW, hzW, hks⟩)
    hdliftlocal' hfirstjet hdliftjet'
  simpa only [hop, Function.comp_apply, ContinuousLinearMap.bilinearComp,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.flip_flip] using hsecond

end Poincare.Analysis.Calculus
