import PoincareConjecture.Proofs.M28.Mathlib.WithinComposition
import PoincareConjecture.Proofs.M28.Mathlib.WithinBilinear
import PoincareConjecture.Proofs.M28.Mathlib.WithinJetsOfAmbient
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.SpacetimePullback

set_option autoImplicit false

open Set Filter Poincare.Analysis.Calculus
open scoped ContDiff Topology

theorem tendstoUniformlyOn_withinJets_spacetime_bilinear_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J : Set ℝ} {U V : Set E} (hJ : UniqueDiffOn ℝ J) (hconvJ : Convex ℝ J)
    (hU : IsOpen U) (hV : IsOpen V) (hconvV : Convex ℝ V) (hVU : V ⊆ U)
    [LocallyCompactSpace (J ×ˢ V)]
    {a : ℕ → E → E} {B : ℕ → ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {B₀ : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    (ha : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k) V)
    (hmap : ∀ᶠ k in atTop, MapsTo (a k) V U)
    (hB : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (B k) (J ×ˢ U))
    (hB₀ : ContDiffOn ℝ ∞ B₀ (J ×ˢ U))
    (hajet : ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (a k)) (iteratedFDeriv ℝ m id) atTop K)
    (hBjet : ∀ m K, IsCompact K → K ⊆ J ×ˢ U → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (B k) (J ×ˢ U))
      (iteratedFDerivWithin ℝ m B₀ (J ×ˢ U)) atTop K) :
    (∀ᶠ k in atTop, ContDiffOn ℝ ∞
      (fun p : ℝ × E => (B k (p.1, a k p.2)).bilinearComp
        (fderiv ℝ (a k) p.2) (fderiv ℝ (a k) p.2)) (J ×ˢ V)) ∧
      ∀ m K, IsCompact K → K ⊆ J ×ˢ V → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m
          (fun p : ℝ × E => (B k (p.1, a k p.2)).bilinearComp
            (fderiv ℝ (a k) p.2) (fderiv ℝ (a k) p.2)) (J ×ˢ V))
        (iteratedFDerivWithin ℝ m B₀ (J ×ˢ V)) atTop K := by
  have hS := hJ.prod hV.uniqueDiffOn
  have hconv := hconvJ.prod hconvV
  have halocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (a k) W := fun x hx => ⟨V, hV, hx, ha⟩
  obtain ⟨_, hliftjet⟩ := smooth_convergence_spacetime_lift hV halocal hajet
  have hlift : ∀ᶠ k in atTop, ContDiffOn ℝ ∞
      (fun p : ℝ × E => (p.1, a k p.2)) ((Prod.snd : ℝ × E → E) ⁻¹' V) := by
    filter_upwards [ha] with k hk
    exact contDiff_fst.contDiffOn.prodMk (hk.comp contDiff_snd.contDiffOn (fun _ hx => hx))
  have hliftwithin : ∀ m K, IsCompact K → K ⊆ J ×ˢ V → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (fun p : ℝ × E => (p.1, a k p.2)) (J ×ˢ V))
      (iteratedFDerivWithin ℝ m id (J ×ˢ V)) atTop K := by
    intro m K hK hKS
    apply (hliftjet m K hK (fun p hp => (hKS hp).2)).withinJets_of_ambient hS hKS
    · filter_upwards [hlift] with k hk p hp
      exact (hk.contDiffAt ((hV.preimage continuous_snd).mem_nhds (hKS hp).2)).of_le
        (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
    · exact fun _ _ => contDiffAt_id
  have hcapture : ∀ K, IsCompact K → K ⊆ J ×ˢ V → ∃ C : Set (ℝ × E),
      IsCompact C ∧ C ⊆ J ×ˢ U ∧ ∀ᶠ k in atTop,
        MapsTo (fun p : ℝ × E => (p.1, a k p.2)) K C := by
    intro K hK hKS
    have hKV : Prod.snd '' K ⊆ V := by rintro _ ⟨p, hp, rfl⟩; exact (hKS hp).2
    have hazero : TendstoUniformlyOn a id atTop (Prod.snd '' K) := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
        (ContinuousMultilinearMap.uniformContinuous_eval_const
          (0 : Fin 0 → E)).comp_tendstoUniformlyOn (hajet 0 _ (hK.image continuous_snd) hKV)
    obtain ⟨C, hC, hCU, hcap⟩ := exists_compact_target_of_tendstoUniformlyOn
      (hK.image continuous_snd) hU continuous_id.continuousOn (hKV.trans hVU) hazero
    refine ⟨(Prod.fst '' K) ×ˢ C, (hK.image continuous_fst).prod hC, ?_, ?_⟩
    · rintro p ⟨⟨q, hq, hqp⟩, hp⟩
      exact ⟨hqp ▸ (hKS hq).1, hCU hp⟩
    · exact hcap.mono fun k hk p hp => ⟨⟨p, hp, rfl⟩, hk ⟨p, hp, rfl⟩⟩
  have hsubset : J ×ˢ V ⊆ J ×ˢ U := prod_mono_right hVU
  obtain ⟨hC, hCjet⟩ := tendstoUniformlyOn_withinJets_comp_of_compact_capture
    hconv hS (hJ.prod hU.uniqueDiffOn) hB₀ contDiff_id.contDiffOn hB
    (hlift.mono fun _ hk => hk.mono fun _ hp => hp.2)
    (hmap.mono fun _ hk _ hp => ⟨hp.1, hk hp.2⟩) hsubset
    hcapture hBjet hliftwithin
  have hd : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fderiv ℝ (a k)) V :=
    ha.mono fun _ hk => hk.fderiv_of_isOpen hV (by simp)
  have hdjet : ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fderiv ℝ (a k)))
      (iteratedFDeriv ℝ m (fun _ : E => ContinuousLinearMap.id ℝ E)) atTop K := by
    intro m K hK hKV
    have hid : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
      funext fun _ => fderiv_id
    simpa only [hid] using tendstoUniformlyOn_fderiv_jets m (hajet (m + 1) K hK hKV)
  obtain ⟨_, hdliftjet⟩ := smooth_convergence_comp_continuousLinearMap
    (ContinuousLinearMap.snd ℝ ℝ E) hV contDiff_const.contDiffOn
    (fun x hx => ⟨V, hV, hx, hd⟩) hdjet
  have hdlift : ∀ᶠ k in atTop, ContDiffOn ℝ ∞
      (fun p : ℝ × E => fderiv ℝ (a k) p.2) ((Prod.snd : ℝ × E → E) ⁻¹' V) :=
    hd.mono fun _ hk => hk.comp contDiff_snd.contDiffOn (fun _ hx => hx)
  have hdwithin : ∀ m K, IsCompact K → K ⊆ J ×ˢ V → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m (fun p : ℝ × E => fderiv ℝ (a k) p.2) (J ×ˢ V))
      (iteratedFDerivWithin ℝ m (fun _ : ℝ × E => ContinuousLinearMap.id ℝ E)
        (J ×ˢ V)) atTop K := by
    intro m K hK hKS
    apply (hdliftjet m K hK (fun p hp => (hKS hp).2)).withinJets_of_ambient hS hKS
    · filter_upwards [hdlift] with k hk p hp
      exact (hk.contDiffAt ((hV.preimage continuous_snd).mem_nhds (hKS hp).2)).of_le
        (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
    · exact fun _ _ => contDiffAt_const
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
  have hdS : ∀ᶠ k in atTop, ContDiffOn ℝ ∞
      (fun p : ℝ × E => fderiv ℝ (a k) p.2) (J ×ˢ V) :=
    hdlift.mono fun _ hk => hk.mono (fun _ hp => hp.2)
  obtain ⟨hfirst, hfirstjet⟩ := tendstoUniformlyOn_withinJets_bilinear hconv hS op
    (hB₀.mono hsubset) contDiff_const.contDiffOn hC hdS hCjet hdwithin
  have hfirst₀ : ContDiffOn ℝ ∞
      (fun p => op (B₀ p) (ContinuousLinearMap.id ℝ E)) (J ×ˢ V) :=
    op.isBoundedBilinearMap.contDiff.comp₂_contDiffOn
      (hB₀.mono hsubset) contDiff_const.contDiffOn
  have hsecond := tendstoUniformlyOn_withinJets_bilinear hconv hS op hfirst₀
    contDiff_const.contDiffOn hfirst hdS hfirstjet hdwithin
  simpa only [hop, Function.comp_apply, ContinuousLinearMap.bilinearComp,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.flip_flip] using hsecond
