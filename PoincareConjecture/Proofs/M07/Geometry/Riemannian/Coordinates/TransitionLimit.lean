import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.UniformSpace.UniformApproximation













set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateTransition

variable {E F G : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedAddCommGroup G]

omit [NormedAddCommGroup E] in


theorem comp_eq_of_tendsto
    {U : Set E} {V : Set F} (hV : IsOpen V)
    {fseq : ℕ → E → F} {f : E → F}
    {gseq : ℕ → F → G} {g : F → G}
    {hseq : ℕ → E → G} {h : E → G}
    (hg : TendstoLocallyUniformlyOn gseq g atTop V)
    (hgcont : ContinuousOn g V) (hfV : MapsTo f U V)
    (hf : ∀ x ∈ U, Tendsto (fun k => fseq k x) atTop (𝓝 (f x)))
    (hh : ∀ x ∈ U, Tendsto (fun k => hseq k x) atTop (𝓝 (h x)))
    (hcomp : ∀ x ∈ U, ∀ᶠ k in atTop, gseq k (fseq k x) = hseq k x) :
    EqOn (g ∘ f) h U := by
  intro x hx
  have hlimit := hg.tendsto_comp (hgcont (f x) (hfV hx)) (hfV hx)
    (tendsto_nhdsWithin_iff.mpr
      ⟨hf x hx, (hf x hx).eventually (hV.mem_nhds (hfV hx))⟩)
  exact tendsto_nhds_unique hlimit
    ((hh x hx).congr' ((hcomp x hx).mono fun k hk => hk.symm))



theorem leftInvOn_of_tendsto
    {U : Set E} {V : Set F} (hV : IsOpen V)
    {fseq : ℕ → E → F} {f : E → F}
    {gseq : ℕ → F → E} {g : F → E}
    (hg : TendstoLocallyUniformlyOn gseq g atTop V)
    (hgcont : ContinuousOn g V) (hfV : MapsTo f U V)
    (hf : ∀ x ∈ U, Tendsto (fun k => fseq k x) atTop (𝓝 (f x)))
    (hinv : ∀ x ∈ U, ∀ᶠ k in atTop, gseq k (fseq k x) = x) :
    LeftInvOn g f U := by
  intro x hx
  exact comp_eq_of_tendsto (hseq := fun _ => id) (h := id) hV hg hgcont hfV hf
    (fun _ _ => tendsto_const_nhds) hinv hx



theorem injOn_of_tendsto_inverse
    {U : Set E} {V : Set F} (hV : IsOpen V)
    {fseq : ℕ → E → F} {f : E → F}
    {gseq : ℕ → F → E} {g : F → E}
    (hg : TendstoLocallyUniformlyOn gseq g atTop V)
    (hgcont : ContinuousOn g V) (hfV : MapsTo f U V)
    (hf : ∀ x ∈ U, Tendsto (fun k => fseq k x) atTop (𝓝 (f x)))
    (hinv : ∀ x ∈ U, ∀ᶠ k in atTop, gseq k (fseq k x) = x) :
    InjOn f U :=
  (leftInvOn_of_tendsto hV hg hgcont hfV hf hinv).injOn

variable [NormedSpace ℝ E] [NormedSpace ℝ F]



theorem pullback_eq_of_tendsto
    {U : Set E} {V : Set F} (hV : IsOpen V)
    {Aseq : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ}
    {A : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Bseq : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ}
    {B : F → F →L[ℝ] F →L[ℝ] ℝ}
    {fseq : ℕ → E → F} {f : E → F}
    (hA : ∀ x ∈ U, ∀ v w,
      Tendsto (fun k => Aseq k x v w) atTop (𝓝 (A x v w)))
    (hB : TendstoLocallyUniformlyOn Bseq B atTop V)
    (hBcont : ContinuousOn B V) (hfV : MapsTo f U V)
    (hf : ∀ x ∈ U, Tendsto (fun k => fseq k x) atTop (𝓝 (f x)))
    (hD : ∀ x ∈ U, ∀ v, Tendsto (fun k => fderiv ℝ (fseq k) x v) atTop
      (𝓝 (fderiv ℝ f x v)))
    (hmetric : ∀ x ∈ U, ∀ᶠ k in atTop, ∀ v w,
      Bseq k (fseq k x) (fderiv ℝ (fseq k) x v) (fderiv ℝ (fseq k) x w) =
        Aseq k x v w) :
    ∀ x ∈ U, ∀ v w,
      B (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) = A x v w := by
  intro x hx v w
  have hcoeff := hB.tendsto_comp (hBcont (f x) (hfV hx)) (hfV hx)
    (tendsto_nhdsWithin_iff.mpr
      ⟨hf x hx, (hf x hx).eventually (hV.mem_nhds (hfV hx))⟩)
  have hv := hD x hx v
  have hw := hD x hx w
  have hfirst := isBoundedBilinearMap_apply.continuous.tendsto
    (B (f x), fderiv ℝ f x v) |>.comp (hcoeff.prodMk_nhds hv)
  have hvalue := isBoundedBilinearMap_apply.continuous.tendsto
    (B (f x) (fderiv ℝ f x v), fderiv ℝ f x w) |>.comp (hfirst.prodMk_nhds hw)
  exact tendsto_nhds_unique hvalue
    ((hA x hx v w).congr' ((hmetric x hx).mono fun k hk => (hk v w).symm))



theorem locallyUniformly_of_tendsto_zeroJet [LocallyCompactSpace E]
    {U : Set E} (hU : IsOpen U) {fseq : ℕ → E → F} {f : E → F}
    (hjet : ∀ K, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ 0 (fseq k))
        (iteratedFDeriv ℝ 0 f) atTop K) :
    TendstoLocallyUniformlyOn fseq f atTop U := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
  intro K hKU hK
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
    (ContinuousMultilinearMap.uniformContinuous_eval_const (0 : Fin 0 → E)).comp_tendstoUniformlyOn
      (hjet K hK hKU)



theorem exists_openPartialHomeomorph_of_tendsto_jets
    [LocallyCompactSpace E] [LocallyCompactSpace F]
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {fseq : ℕ → E → F} {f : E → F} {gseq : ℕ → F → E} {g : F → E}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g V)
    (hfV : MapsTo f U V) (hgU : MapsTo g V U)
    (hfjet : ∀ (m : ℕ) K, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fseq k))
        (iteratedFDeriv ℝ m f) atTop K)
    (hgjet : ∀ (m : ℕ) K, IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (gseq k))
        (iteratedFDeriv ℝ m g) atTop K)
    (hleft : ∀ x ∈ U, ∀ᶠ k in atTop, gseq k (fseq k x) = x)
    (hright : ∀ y ∈ V, ∀ᶠ k in atTop, fseq k (gseq k y) = y) :
    ∃ e : OpenPartialHomeomorph E F,
      e.source = U ∧ e.target = V ∧ (⇑e) = f ∧ (⇑e.symm) = g ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hfconv := locallyUniformly_of_tendsto_zeroJet hU (hfjet 0)
  have hgconv := locallyUniformly_of_tendsto_zeroJet hV (hgjet 0)
  let e : OpenPartialHomeomorph E F :=
    { toFun := f
      invFun := g
      source := U
      target := V
      map_source' := hfV
      map_target' := hgU
      left_inv' := leftInvOn_of_tendsto hV hgconv hg.continuousOn hfV
        (fun x hx => hfconv.tendsto_at hx) hleft
      right_inv' := leftInvOn_of_tendsto hU hfconv hf.continuousOn hgU
        (fun y hy => hgconv.tendsto_at hy) hright
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hg.continuousOn
      open_source := hU
      open_target := hV }
  exact ⟨e, rfl, rfl, rfl, rfl, hf, hg⟩




theorem pullback_eq_of_tendsto_jets [LocallyCompactSpace E] [LocallyCompactSpace F]
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    {Aseq : ℕ → E → E →L[ℝ] E →L[ℝ] ℝ}
    {A : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Bseq : ℕ → F → F →L[ℝ] F →L[ℝ] ℝ}
    {B : F → F →L[ℝ] F →L[ℝ] ℝ}
    {fseq : ℕ → E → F} {f : E → F}
    (hA : ∀ (m : ℕ) K, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Aseq k))
        (iteratedFDeriv ℝ m A) atTop K)
    (hB : ∀ (m : ℕ) K, IsCompact K → K ⊆ V →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (Bseq k))
        (iteratedFDeriv ℝ m B) atTop K)
    (hf : ∀ (m : ℕ) K, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fseq k))
        (iteratedFDeriv ℝ m f) atTop K)
    (hBcont : ContinuousOn B V) (hfV : MapsTo f U V)
    (hmetric : ∀ x ∈ U, ∀ᶠ k in atTop, ∀ v w,
      Bseq k (fseq k x) (fderiv ℝ (fseq k) x v) (fderiv ℝ (fseq k) x w) =
        Aseq k x v w) :
    ∀ x ∈ U, ∀ v w,
      B (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) = A x v w := by
  apply pullback_eq_of_tendsto hV ?_
    (locallyUniformly_of_tendsto_zeroJet hV (hB 0)) hBcont hfV
    (fun x hx => (locallyUniformly_of_tendsto_zeroJet hU (hf 0)).tendsto_at hx)
    ?_ hmetric
  · intro x hx v w
    exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).continuous.tendsto _).comp
        ((locallyUniformly_of_tendsto_zeroJet hU (hA 0)).tendsto_at hx))
  · intro x hx v
    have hpoint := (hf 1 {x} isCompact_singleton (singleton_subset_iff.mpr hx)).tendsto_at
      (mem_singleton x)
    have hev := ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (F := F) (fun _ : Fin 1 => v)
    simpa only [Function.comp_def, iteratedFDeriv_one_apply] using
      (hev.continuous.tendsto _).comp hpoint

end PoincareConjecture.CoordinateTransition
