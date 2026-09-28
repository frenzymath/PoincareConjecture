import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Uniqueness

set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

theorem eventually_contDiffAt_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} {f : ℕ → E → F} (hK : IsCompact K) (hKU : K ⊆ U)
    (hlocal : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) V) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ContDiffAt ℝ ∞ (f k) x := by
  refine hK.induction_on (p := fun S => ∀ᶠ k in atTop,
    ∀ x ∈ S, ContDiffAt ℝ ∞ (f k) x) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (by simp)
  · intro S T hST hT
    exact hT.mono fun _ hk x hx => hk x (hST hx)
  · intro S T hS hT
    filter_upwards [hS, hT] with k hkS hkT x hx
    exact hx.elim (hkS x) (hkT x)
  · intro x hx
    obtain ⟨V, hV, hxV, hVsmooth⟩ := hlocal x (hKU hx)
    exact ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV),
      hVsmooth.mono fun _ hk _ hy => hk.contDiffAt (hV.mem_nhds hy)⟩

private theorem locallyUniformly_of_zeroJet
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → F} {f₀ : EuclideanSpace ℝ (Fin d) → F}
    (hjet : ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ 0 (f k)) (iteratedFDeriv ℝ 0 f₀) atTop K) :
    TendstoLocallyUniformlyOn f f₀ atTop U := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
  intro K hKU hK
  simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
    (ContinuousMultilinearMap.uniformContinuous_eval_const (0 : Fin 0 →
      EuclideanSpace ℝ (Fin d))).comp_tendstoUniformlyOn (hjet K hK hKU)

theorem smooth_convergence_comp_on_open
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hV : IsOpen V)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → F}
    {g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {f₀ : EuclideanSpace ℝ (Fin d) → F}
    {g₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
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
  have hfconv := locallyUniformly_of_zeroJet hU (hfjet 0)
  have hgconv := locallyUniformly_of_zeroJet hV (hgjet 0)
  have hgc (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsCompact K) (hKV : K ⊆ V) :
      TendstoUniformlyOn g g₀ atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hgconv.mono hKV)
  have hfb := locallyEventuallyBoundedDerivatives_of_tendsto_jets hU hf₀ hfjet
  have hgb := locallyEventuallyBoundedDerivatives_of_tendsto_jets hV hg₀ hgjet
  have hlocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k ∘ g k) W := by
    intro x hx
    obtain ⟨K, hK, hxK, hKV⟩ := exists_compact_between isCompact_singleton hV
      (singleton_subset_iff.mpr hx)
    obtain ⟨T, hT, hTU, hmap⟩ := exists_compact_target_of_tendstoUniformlyOn hK hU
      (hg₀.continuousOn.mono hKV) (hgU.mono_left hKV) (hgc K hK hKV)
    refine ⟨interior K, isOpen_interior, hxK (mem_singleton x), interior_subset.trans hKV, ?_⟩
    filter_upwards [hmap,
      eventually_contDiffAt_on_compact hT hTU hflocal,
      eventually_contDiffAt_on_compact hK hKV hglocal]
      with k hkmap hkf hkg y hy
    exact ((hkf _ (hkmap (interior_subset hy))).comp y
      (hkg y (interior_subset hy))).contDiffWithinAt
  refine ⟨hlocal, fun m K hK hKV => ?_⟩
  have hbound : LocallyEventuallyBoundedDerivatives V (fun k => f k ∘ g k) := by
    intro C hC hCV l
    obtain ⟨T, hT, hTU, hmap⟩ := exists_compact_target_of_tendstoUniformlyOn hC hU
      (hg₀.continuousOn.mono hCV) (hgU.mono_left hCV) (hgc C hC hCV)
    obtain ⟨A, _, hA⟩ := hfb.bound_all hT hTU l
    obtain ⟨B, _, hB⟩ := hgb.bound_all hC hCV l
    refine ⟨l.factorial * A * (max B 1) ^ l, ?_⟩
    filter_upwards [hmap, hA, hB,
      eventually_contDiffAt_on_compact hT hTU hflocal,
      eventually_contDiffAt_on_compact hC hCV hglocal]
      with k hkmap hkA hkB hkf hkg x hx
    apply norm_iteratedFDeriv_comp_le_of_contDiffAt (hkg x hx) (hkf _ (hkmap hx)) l
      (fun r hr => hkA r hr _ (hkmap hx))
    intro r hr hrl
    exact (hkB r hrl x hx).trans ((le_max_left _ _).trans
      (le_self_pow₀ (le_max_right B 1) (Nat.ne_of_gt hr)))
  have hpoint (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ V) :
      Tendsto (fun k => (f k ∘ g k) x) atTop (𝓝 ((f₀ ∘ g₀) x)) :=
    hfconv.tendsto_comp (hf₀.continuousOn _ (hgU hx)) (hgU hx)
      (tendsto_nhdsWithin_iff.mpr ⟨hgconv.tendsto_at hx,
        (hgconv.tendsto_at hx).eventually (hU.mem_nhds (hgU hx))⟩)
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((tendstoLocallyUniformlyOn_iteratedFDeriv_of_locally_eventually_smooth
      hpoint hlocal hbound m).mono hKV)

theorem tendstoUniformlyOn_fderiv_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℕ → E → F} {f₀ : E → F} {K : Set E} (m : ℕ)
    (hjet : TendstoUniformlyOn (fun k => iteratedFDeriv ℝ (m + 1) (f k))
      (iteratedFDeriv ℝ (m + 1) f₀) atTop K) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fderiv ℝ (f k)))
      (iteratedFDeriv ℝ m (fderiv ℝ f₀)) atTop K := by
  have heq (q : E → F) : (fun x => continuousMultilinearCurryRightEquiv' ℝ m E F
      (iteratedFDeriv ℝ (m + 1) q x)) = iteratedFDeriv ℝ m (fderiv ℝ q) := by
    funext x
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  simpa only [Function.comp_def, heq] using
    (continuousMultilinearCurryRightEquiv' ℝ m E F).isometry.uniformContinuous.comp_tendstoUniformlyOn hjet

private theorem norm_iteratedFDeriv_bilinear_le_at
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => B (f y) (g y)) x‖ ≤
      ‖B‖ * ∑ l ∈ Finset.range (m + 1), (m.choose l : ℝ) *
        ‖iteratedFDeriv ℝ l f x‖ * ‖iteratedFDeriv ℝ (m - l) g x‖ := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨t, ht, hgt⟩ := hg.contDiffOn (m := (m : ℕ∞ω)) (by exact_mod_cast le_top) (by simp)
  obtain ⟨v, hv, hvo, hxv⟩ := mem_nhds_iff.mp (inter_mem hs ht)
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear
    (hfs.mono (fun _ hy => (hv hy).1)) (hgt.mono (fun _ hy => (hv hy).2))
    hvo.uniqueDiffOn hxv (le_refl (m : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hvo hxv] using h

theorem smooth_convergence_bilinear_on_open
    {d : ℕ} {F G H : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (B : F →L[ℝ] G →L[ℝ] H)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → F} {f₀ : EuclideanSpace ℝ (Fin d) → F}
    {g : ℕ → EuclideanSpace ℝ (Fin d) → G} {g₀ : EuclideanSpace ℝ (Fin d) → G}
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
  have hlocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fun y => B (f k y) (g k y)) W := by
    intro x hx
    obtain ⟨V, hV, hxV, hf⟩ := hflocal x hx
    obtain ⟨W, hW, hxW, hg⟩ := hglocal x hx
    refine ⟨U ∩ V ∩ W, (hU.inter hV).inter hW, ⟨⟨hx, hxV⟩, hxW⟩,
      fun _ hy => hy.1.1, ?_⟩
    filter_upwards [hf, hg] with k hkf hkg
    exact B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn
      (hkf.mono fun _ hy => hy.1.2) (hkg.mono fun _ hy => hy.2)
  refine ⟨hlocal, fun m K hK hKU => ?_⟩
  have hfb := locallyEventuallyBoundedDerivatives_of_tendsto_jets hU hf₀ hfjet
  have hgb := locallyEventuallyBoundedDerivatives_of_tendsto_jets hU hg₀ hgjet
  have hbound : LocallyEventuallyBoundedDerivatives U (fun k y => B (f k y) (g k y)) := by
    intro C hC hCU l
    obtain ⟨A, hA0, hA⟩ := hfb.bound_all hC hCU l
    obtain ⟨D, hD0, hD⟩ := hgb.bound_all hC hCU l
    refine ⟨‖B‖ * ∑ r ∈ Finset.range (l + 1), (l.choose r : ℝ) * A * D, ?_⟩
    filter_upwards [hA, hD,
      eventually_contDiffAt_on_compact hC hCU hflocal,
      eventually_contDiffAt_on_compact hC hCU hglocal]
      with k hkA hkD hkf hkg x hx
    refine (norm_iteratedFDeriv_bilinear_le_at B (hkf x hx) (hkg x hx) l).trans ?_
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
    apply Finset.sum_le_sum
    intro r hr
    have hrl := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hkA r hrl x hx) (by positivity))
      (hkD (l - r) (Nat.sub_le _ _) x hx) (norm_nonneg _) (by positivity)
  have hfpoint := locallyUniformly_of_zeroJet hU (hfjet 0)
  have hgpoint := locallyUniformly_of_zeroJet hU (hgjet 0)
  have hpoint (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ U) :
      Tendsto (fun k => B (f k x) (g k x)) atTop (𝓝 (B (f₀ x) (g₀ x))) :=
    (B.isBoundedBilinearMap.continuous.tendsto (f₀ x, g₀ x)).comp
      ((hfpoint.tendsto_at hx).prodMk_nhds (hgpoint.tendsto_at hx))
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((tendstoLocallyUniformlyOn_iteratedFDeriv_of_locally_eventually_smooth
      hpoint hlocal hbound m).mono hKU)

theorem smooth_convergence_pullback_bilinear_on_open
    {d : ℕ} {U V : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hV : IsOpen V)
    {B : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {B₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {a : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {a₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
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
  let E := EuclideanSpace ℝ (Fin d)
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
  obtain ⟨hClocal, hCjet⟩ := smooth_convergence_comp_on_open hU hV hB₀ ha₀ haU
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
  obtain ⟨hfirstlocal, hfirstjet⟩ := smooth_convergence_bilinear_on_open hV op hC₀ hd₀
    (fun x hx => let ⟨W, hW, hxW, _, hks⟩ := hClocal x hx; ⟨W, hW, hxW, hks⟩)
    hdlocal hCjet hdjet
  have hfirst₀ : ContDiffOn ℝ ∞ (fun y => op (B₀ (a₀ y)) (fderiv ℝ a₀ y)) V :=
    op.isBoundedBilinearMap.contDiff.comp₂_contDiffOn hC₀ hd₀
  have hsecond := smooth_convergence_bilinear_on_open hV op hfirst₀ hd₀
    (fun x hx => let ⟨W, hW, hxW, _, hks⟩ := hfirstlocal x hx; ⟨W, hW, hxW, hks⟩)
    hdlocal hfirstjet hdjet
  simpa only [hop, Function.comp_apply, ContinuousLinearMap.bilinearComp] using hsecond

end Poincare.Analysis.Calculus
