import PoincareLib.Analysis.Calculus.SmoothCompactness.Pullback
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Smooth convergence under linear changes of domain

Continuous linear equivalences transport every iterated derivative by
precomposition in all its arguments. Consequently compact-uniform convergence
of all jets and local eventual smoothness do not depend on the chosen linear
coordinates. In particular finite-dimensional product domains may retain their
given norm when using Euclidean-domain smooth compactness results.
-/

set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

variable {E E' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The ambient jet transformation is exact even for nonsmooth total maps. -/
theorem iteratedFDeriv_comp_continuousLinearEquiv
    (e : E' ≃L[ℝ] E) (f : E → F) (m : ℕ) (x : E') :
    iteratedFDeriv ℝ m (f ∘ e) x =
      (iteratedFDeriv ℝ m f (e x)).compContinuousLinearMap
        (fun _ => e.toContinuousLinearMap) := by
  simpa only [preimage_univ, iteratedFDerivWithin_univ] using
    e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (e x)) m

/-- The jet norm changes by at most the `m`th power of the coordinate map norm. -/
theorem norm_iteratedFDeriv_comp_continuousLinearEquiv_le
    (e : E' ≃L[ℝ] E) (f : E → F) (m : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ m (f ∘ e) x‖ ≤
      ‖iteratedFDeriv ℝ m f (e x)‖ * ‖e.toContinuousLinearMap‖ ^ m := by
  rw [iteratedFDeriv_comp_continuousLinearEquiv]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ m f (e x)).norm_compContinuousLinearMap_le
      (fun _ : Fin m => e.toContinuousLinearMap)

/-- Uniform convergence of a jet on the image set transports to the domain. -/
theorem tendstoUniformlyOn_jet_comp_continuousLinearEquiv
    (e : E' ≃L[ℝ] E) {f : ℕ → E → F} {f₀ : E → F} {K : Set E'} (m : ℕ)
    (hjet : TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
      (iteratedFDeriv ℝ m f₀) atTop (e '' K)) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k ∘ e))
      (iteratedFDeriv ℝ m (f₀ ∘ e)) atTop K := by
  have hcomp := (hjet.comp e).mono (subset_preimage_image (⇑e) K)
  have h := (ContinuousMultilinearMap.compContinuousLinearMapL
    (F := F) (fun _ : Fin m => e.toContinuousLinearMap)).uniformContinuous.comp_tendstoUniformlyOn hcomp
  change TendstoUniformlyOn (fun k x => iteratedFDeriv ℝ m (f k ∘ e) x)
    (fun x => iteratedFDeriv ℝ m (f₀ ∘ e) x) atTop K
  simp_rw [iteratedFDeriv_comp_continuousLinearEquiv]
  exact h

/-- Compact-uniform convergence of all jets transports through a fixed linear
change of coordinates. -/
theorem compact_jet_convergence_comp_continuousLinearEquiv
    (e : E' ≃L[ℝ] E) {U : Set E} {f : ℕ → E → F} {f₀ : E → F}
    (hjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m f₀) atTop K) :
    ∀ m K, IsCompact K → K ⊆ e ⁻¹' U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k ∘ e))
      (iteratedFDeriv ℝ m (f₀ ∘ e)) atTop K := by
  intro m K hK hKU
  exact tendstoUniformlyOn_jet_comp_continuousLinearEquiv e m
    (hjet m (e '' K) (hK.image e.continuous) (image_subset_iff.mpr hKU))

/-- All compact jets converge in one system of linear coordinates if and only
if they converge in another. No smoothness premise is needed for this transfer. -/
theorem compact_jet_convergence_comp_continuousLinearEquiv_iff
    (e : E' ≃L[ℝ] E) {U : Set E} {f : ℕ → E → F} {f₀ : E → F} :
    (∀ m K, IsCompact K → K ⊆ e ⁻¹' U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k ∘ e))
      (iteratedFDeriv ℝ m (f₀ ∘ e)) atTop K) ↔
    (∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m f₀) atTop K) := by
  refine ⟨fun h => ?_, compact_jet_convergence_comp_continuousLinearEquiv e⟩
  have hback := compact_jet_convergence_comp_continuousLinearEquiv e.symm h
  simpa [Function.comp_def] using hback

/-- Eventual smoothness on a neighborhood of each point transports through a
fixed continuous linear equivalence. -/
theorem locally_eventually_smooth_comp_continuousLinearEquiv
    (e : E' ≃L[ℝ] E) {U : Set E} {f : ℕ → E → F}
    (hlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W) :
    ∀ x ∈ e ⁻¹' U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ e) W := by
  intro x hx
  obtain ⟨W, hW, hxW, hks⟩ := hlocal (e x) hx
  exact ⟨e ⁻¹' W, hW.preimage e.continuous, hxW,
    hks.mono fun k hk => hk.comp_continuousLinearMap e.toContinuousLinearMap⟩

/-- Local eventual smoothness is independent of the chosen linear coordinates. -/
theorem locally_eventually_smooth_comp_continuousLinearEquiv_iff
    (e : E' ≃L[ℝ] E) {U : Set E} {f : ℕ → E → F} :
    (∀ x ∈ e ⁻¹' U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ e) W) ↔
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W) := by
  refine ⟨fun h => ?_, locally_eventually_smooth_comp_continuousLinearEquiv e⟩
  have hback := locally_eventually_smooth_comp_continuousLinearEquiv e.symm h
  simpa [Function.comp_def] using hback

/-- A fixed linear change of codomain also transports all jets, without
requiring differentiability of the approximating total maps. -/
theorem compact_jet_convergence_continuousLinearEquiv_comp
    (e : E ≃L[ℝ] E') {U : Set F} {f : ℕ → F → E} {f₀ : F → E}
    (hjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m f₀) atTop K) :
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (e ∘ f k))
      (iteratedFDeriv ℝ m (e ∘ f₀)) atTop K := by
  intro m K hK hKU
  let L := (e.continuousMultilinearMapCongrRight (fun _ : Fin m => F)).toContinuousLinearMap
  have h := L.uniformContinuous.comp_tendstoUniformlyOn (hjet m K hK hKU)
  change TendstoUniformlyOn (fun k x => iteratedFDeriv ℝ m (e ∘ f k) x)
    (fun x => iteratedFDeriv ℝ m (e ∘ f₀) x) atTop K
  simp_rw [ContinuousLinearEquiv.iteratedFDeriv_comp_left]
  exact h

/-- Bilinear smooth convergence on any finite-dimensional normed domain,
including product domains with their original product norm. -/
theorem smooth_convergence_bilinear_on_finiteDimensional
    [FiniteDimensional ℝ E]
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    {U : Set E} (hU : IsOpen U) (B : F →L[ℝ] G →L[ℝ] H)
    {f : ℕ → E → F} {f₀ : E → F} {g : ℕ → E → G} {g₀ : E → G}
    (hf₀ : ContDiffOn ℝ ∞ f₀ U) (hg₀ : ContDiffOn ℝ ∞ g₀ U)
    (hflocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hglocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (g k) W)
    (hfjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m f₀) atTop K)
    (hgjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (g k)) (iteratedFDeriv ℝ m g₀) atTop K) :
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fun y => B (f k y) (g k y)) W) ∧
      ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (fun y => B (f k y) (g k y)))
        (iteratedFDeriv ℝ m (fun y => B (f₀ y) (g₀ y))) atTop K := by
  let e := (toEuclidean (E := E)).symm
  obtain ⟨hlocal, hjet⟩ := smooth_convergence_bilinear_on_open
    (hU.preimage e.continuous) B
    (hf₀.comp_continuousLinearMap e.toContinuousLinearMap)
    (hg₀.comp_continuousLinearMap e.toContinuousLinearMap)
    (locally_eventually_smooth_comp_continuousLinearEquiv e hflocal)
    (locally_eventually_smooth_comp_continuousLinearEquiv e hglocal)
    (compact_jet_convergence_comp_continuousLinearEquiv e hfjet)
    (compact_jet_convergence_comp_continuousLinearEquiv e hgjet)
  refine ⟨?_, (compact_jet_convergence_comp_continuousLinearEquiv_iff e).mp hjet⟩
  have hback := (locally_eventually_smooth_comp_continuousLinearEquiv_iff
    (f := fun k y => B (f k y) (g k y)) e).mp
    (fun x hx => let ⟨W, hW, hxW, _, hks⟩ := hlocal x hx; ⟨W, hW, hxW, hks⟩)
  intro x hx
  obtain ⟨W, hW, hxW, hks⟩ := hback x hx
  exact ⟨U ∩ W, hU.inter hW, ⟨hx, hxW⟩, inter_subset_left,
    hks.mono fun k hk => hk.mono inter_subset_right⟩

/-- Varying composition on a finite-dimensional normed domain, without changing
its chosen norm or requiring globally smooth approximations. -/
theorem smooth_convergence_comp_on_finiteDimensional
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℕ → E → F} {g : ℕ → E → E} {f₀ : E → F} {g₀ : E → E}
    (hf₀ : ContDiffOn ℝ ∞ f₀ U) (hg₀ : ContDiffOn ℝ ∞ g₀ V)
    (hgU : MapsTo g₀ V U)
    (hflocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hglocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (g k) W)
    (hfjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m f₀) atTop K)
    (hgjet : ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (g k)) (iteratedFDeriv ℝ m g₀) atTop K) :
    (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ g k) W) ∧
      ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (f k ∘ g k))
        (iteratedFDeriv ℝ m (f₀ ∘ g₀)) atTop K := by
  let e := (toEuclidean (E := E)).symm
  have hgjet' := compact_jet_convergence_continuousLinearEquiv_comp e.symm
    (compact_jet_convergence_comp_continuousLinearEquiv e hgjet)
  have hglocal' : ∀ x ∈ e ⁻¹' V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (e.symm ∘ (g k ∘ e)) W := by
    intro x hx
    obtain ⟨W, hW, hxW, hks⟩ :=
      locally_eventually_smooth_comp_continuousLinearEquiv e hglocal x hx
    exact ⟨W, hW, hxW, hks.mono fun k hk => e.symm.contDiff.comp_contDiffOn hk⟩
  have hgU' : MapsTo (e.symm ∘ (g₀ ∘ e)) (e ⁻¹' V) (e ⁻¹' U) := by
    intro x hx
    simpa only [mem_preimage, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      using hgU hx
  obtain ⟨hlocal, hjet⟩ := smooth_convergence_comp_on_open
    (hU.preimage e.continuous) (hV.preimage e.continuous)
    (hf₀.comp_continuousLinearMap e.toContinuousLinearMap)
    (e.symm.contDiff.comp_contDiffOn (hg₀.comp_continuousLinearMap e.toContinuousLinearMap)) hgU'
    (locally_eventually_smooth_comp_continuousLinearEquiv e hflocal) hglocal'
    (compact_jet_convergence_comp_continuousLinearEquiv e hfjet) hgjet'
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] at hlocal hjet
  refine ⟨?_, (compact_jet_convergence_comp_continuousLinearEquiv_iff e).mp hjet⟩
  have hback := (locally_eventually_smooth_comp_continuousLinearEquiv_iff
    (f := fun k => f k ∘ g k) e).mp
    (fun x hx => let ⟨W, hW, hxW, _, hks⟩ := hlocal x hx; ⟨W, hW, hxW, hks⟩)
  intro x hx
  obtain ⟨W, hW, hxW, hks⟩ := hback x hx
  exact ⟨V ∩ W, hV.inter hW, ⟨hx, hxW⟩, inter_subset_left,
    hks.mono fun k hk => hk.mono inter_subset_right⟩

/-- The actual bilinear pullback converges smoothly on any finite-dimensional
real normed domain, in particular on a spacetime product with its max norm. -/
theorem smooth_convergence_pullback_bilinear_on_finiteDimensional
    [FiniteDimensional ℝ E]
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {B : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ} {B₀ : E → E →L[ℝ] E →L[ℝ] ℝ}
    {a : ℕ → E → E} {a₀ : E → E}
    (hB₀ : ContDiffOn ℝ ∞ B₀ U) (ha₀ : ContDiffOn ℝ ∞ a₀ V)
    (haU : MapsTo a₀ V U)
    (hBlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (B k) W)
    (halocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k) W)
    (hBjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (B k)) (iteratedFDeriv ℝ m B₀) atTop K)
    (hajet : ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m a₀) atTop K) :
    (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ (fun y => (B k (a k y)).bilinearComp
        (fderiv ℝ (a k) y) (fderiv ℝ (a k) y)) W) ∧
      ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (fun y => (B k (a k y)).bilinearComp
          (fderiv ℝ (a k) y) (fderiv ℝ (a k) y)))
        (iteratedFDeriv ℝ m (fun y => (B₀ (a₀ y)).bilinearComp
          (fderiv ℝ a₀ y) (fderiv ℝ a₀ y))) atTop K := by
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
  obtain ⟨hClocal, hCjet⟩ := smooth_convergence_comp_on_finiteDimensional hU hV hB₀ ha₀ haU
    hBlocal halocal hBjet hajet
  have hC₀ : ContDiffOn ℝ ∞ (B₀ ∘ a₀) V := hB₀.comp ha₀ haU
  have hd₀ : ContDiffOn ℝ ∞ (fderiv ℝ a₀) V :=
    ha₀.fderiv_of_isOpen hV (by simp)
  have hdlocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fderiv ℝ (a k)) W := by
    intro x hx
    obtain ⟨W, hW, hxW, hks⟩ := halocal x hx
    exact ⟨W, hW, hxW, hks.mono fun k hk => hk.fderiv_of_isOpen hW (by simp)⟩
  have hdjet : ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fderiv ℝ (a k)))
      (iteratedFDeriv ℝ m (fderiv ℝ a₀)) atTop K :=
    fun m K hK hKV => tendstoUniformlyOn_fderiv_jets m (hajet (m + 1) K hK hKV)
  obtain ⟨hfirstlocal, hfirstjet⟩ := smooth_convergence_bilinear_on_finiteDimensional hV op hC₀ hd₀
    (fun x hx => let ⟨W, hW, hxW, _, hks⟩ := hClocal x hx; ⟨W, hW, hxW, hks⟩)
    hdlocal hCjet hdjet
  have hfirst₀ : ContDiffOn ℝ ∞ (fun y => op (B₀ (a₀ y)) (fderiv ℝ a₀ y)) V :=
    op.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hC₀ hd₀
  have hsecond := smooth_convergence_bilinear_on_finiteDimensional hV op hfirst₀ hd₀
    (fun x hx => let ⟨W, hW, hxW, _, hks⟩ := hfirstlocal x hx; ⟨W, hW, hxW, hks⟩)
    hdlocal hfirstjet hdjet
  simpa only [hop, Function.comp_apply, ContinuousLinearMap.bilinearComp] using hsecond

end Poincare.Analysis.Calculus
