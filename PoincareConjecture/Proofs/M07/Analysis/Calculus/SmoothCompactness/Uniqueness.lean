import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Operations









set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus

private theorem locallyUniformly_of_tendsto_zeroJet
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [LocallyCompactSpace E]
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

theorem contDiffOn_of_locally_eventually_smooth
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → E}
    {F : EuclideanSpace ℝ (Fin d) → E}
    (hpoint : ∀ x ∈ Ω, Tendsto (fun k => f k x) atTop (𝓝 (F x)))
    (hlocal : ∀ x ∈ Ω, ∃ V : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) V)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f) :
    ContDiffOn ℝ ∞ F Ω := by
  intro x hx
  obtain ⟨V, hV, hxV, hVΩ, hVsmooth⟩ := hlocal x hx
  obtain ⟨N, hN⟩ := eventually_atTop.mp hVsmooth
  obtain ⟨S⟩ := exists_smoothSubsequenceExtraction hV (fun k => f (k + N))
    (fun k => hN (k + N) (Nat.le_add_left N k)) (by
      intro K hK hKV m
      obtain ⟨B, hB⟩ := hbound K hK (hKV.trans hVΩ) m
      exact ⟨B, (tendsto_add_atTop_nat N).eventually hB⟩)
  have hzero := locallyUniformly_of_tendsto_zeroJet hV
    (fun K hK hKV => S.iteratedFDeriv_tendsto_uniformlyOn 0 K hK hKV)
  have heq : EqOn F S.limit V := by
    intro y hy
    exact tendsto_nhds_unique
      ((hpoint y (hVΩ hy)).comp
        ((tendsto_add_atTop_nat N).comp S.subsequence_strictMono.tendsto_atTop))
      (hzero.tendsto_at hy)
  exact (((S.limit_contDiffOn.congr heq) x hxV).contDiffAt
    (hV.mem_nhds hxV)).contDiffWithinAt

theorem tendsto_iteratedFDeriv_of_locally_eventually_smooth
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → E}
    {F : EuclideanSpace ℝ (Fin d) → E}
    (hpoint : ∀ x ∈ Ω, Tendsto (fun k => f k x) atTop (𝓝 (F x)))
    (hlocal : ∀ x ∈ Ω, ∃ V : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) V)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f)
    (m : ℕ) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ Ω) :
    Tendsto (fun k => iteratedFDeriv ℝ m (f k) x) atTop
      (𝓝 (iteratedFDeriv ℝ m F x)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨V, hV, hxV, hVΩ, hVsmooth⟩ := hlocal x hx
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hns.eventually hVsmooth)
  have htail := hns.comp (tendsto_add_atTop_nat N)
  obtain ⟨S⟩ := exists_smoothSubsequenceExtraction hV (fun k => f (ns (k + N)))
    (fun k => hN (k + N) (Nat.le_add_left N k)) (by
      intro K hK hKV l
      obtain ⟨B, hB⟩ := hbound K hK (hKV.trans hVΩ) l
      exact ⟨B, htail.eventually hB⟩)
  have hzero := locallyUniformly_of_tendsto_zeroJet hV
    (fun K hK hKV => S.iteratedFDeriv_tendsto_uniformlyOn 0 K hK hKV)
  have heq : EqOn S.limit F V := by
    intro y hy
    exact tendsto_nhds_unique (hzero.tendsto_at hy)
      ((hpoint y (hVΩ hy)).comp (htail.comp S.subsequence_strictMono.tendsto_atTop))
  have hnear : S.limit =ᶠ[𝓝 x] F := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq hy
  refine ⟨fun k => S.subsequence k + N, ?_⟩
  have hjet := (S.iteratedFDeriv_tendsto_uniformlyOn m {x} (isCompact_singleton)
    (singleton_subset_iff.mpr hxV)).tendsto_at (mem_singleton x)
  exact (hnear.iteratedFDeriv ℝ m).self_of_nhds ▸ hjet

theorem tendstoUniformlyOn_iteratedFDeriv_of_eventually_smooth
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {f : ℕ → EuclideanSpace ℝ (Fin d) → E}
    {F : EuclideanSpace ℝ (Fin d) → E}
    (hpoint : ∀ x ∈ Ω, Tendsto (fun k => f k x) atTop (𝓝 (F x)))
    (hsmooth : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) Ω)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f)
    (m : ℕ) {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m F) atTop K := by
  let fs := fun k => UniformFun.ofFun (fun x : K => iteratedFDeriv ℝ m (f k) x)
  let Fs := UniformFun.ofFun (fun x : K => iteratedFDeriv ℝ m F x)
  have ht : Tendsto fs atTop (𝓝 Fs) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hns.eventually hsmooth)
    have htail := hns.comp (tendsto_add_atTop_nat N)
    obtain ⟨S⟩ := exists_smoothSubsequenceExtraction hΩ (fun k => f (ns (k + N)))
      (fun k => hN (k + N) (Nat.le_add_left N k)) (by
        intro A hA hAΩ l
        obtain ⟨B, hB⟩ := hbound A hA hAΩ l
        exact ⟨B, htail.eventually hB⟩)
    have hzero := locallyUniformly_of_tendsto_zeroJet hΩ
      (fun A hA hAΩ => S.iteratedFDeriv_tendsto_uniformlyOn 0 A hA hAΩ)
    have heq : EqOn S.limit F Ω := by
      intro x hx
      exact tendsto_nhds_unique (hzero.tendsto_at hx)
        ((hpoint x hx).comp (htail.comp S.subsequence_strictMono.tendsto_atTop))
    have hjetEq : EqOn (iteratedFDeriv ℝ m S.limit) (iteratedFDeriv ℝ m F) K := by
      intro x hx
      have hnear : S.limit =ᶠ[𝓝 x] F := by
        filter_upwards [hΩ.mem_nhds (hKΩ hx)] with y hy
        exact heq hy
      exact (hnear.iteratedFDeriv ℝ m).self_of_nhds
    refine ⟨fun k => S.subsequence k + N, UniformFun.tendsto_iff_tendstoUniformly.mpr ?_⟩
    exact tendstoUniformlyOn_iff_restrict.mp
      ((S.iteratedFDeriv_tendsto_uniformlyOn m K hK hKΩ).congr_right hjetEq)
  exact tendstoUniformlyOn_iff_restrict.mpr (UniformFun.tendsto_iff_tendstoUniformly.mp ht)

theorem tendstoLocallyUniformlyOn_iteratedFDeriv_of_locally_eventually_smooth
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → E}
    {F : EuclideanSpace ℝ (Fin d) → E}
    (hpoint : ∀ x ∈ Ω, Tendsto (fun k => f k x) atTop (𝓝 (F x)))
    (hlocal : ∀ x ∈ Ω, ∃ V : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) V)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f) (m : ℕ) :
    TendstoLocallyUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
      (iteratedFDeriv ℝ m F) atTop Ω := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  obtain ⟨V, hV, hxV, hVΩ, hVsmooth⟩ := hlocal x hx
  obtain ⟨K, ⟨hKn, hK⟩, hKV⟩ := (compact_basis_nhds x).mem_iff.mp (hV.mem_nhds hxV)
  refine ⟨K, nhdsWithin_le_nhds hKn, ?_⟩
  exact tendstoUniformlyOn_iteratedFDeriv_of_eventually_smooth hV
    (fun y hy => hpoint y (hVΩ hy)) hVsmooth
    (fun A hA hAV l => hbound A hA (hAV.trans hVΩ) l) m hK hKV

theorem tendstoUniformlyOn_cutoff_perturbation_jet
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {f : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hpoint : ∀ x ∈ Ω, Tendsto (fun k => f k x) atTop (𝓝 x))
    (hlocal : ∀ x ∈ Ω, ∃ V : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen V ∧ x ∈ V ∧ ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) V)
    (hbound : LocallyEventuallyBoundedDerivatives Ω f)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (m : ℕ) {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m
      (fun x => x + χ x • (f k x - x))) (iteratedFDeriv ℝ m id) atTop K := by
  have hs : ∀ᶠ k in atTop, ContDiff ℝ ∞ (fun x => x + χ x • (f k x - x)) :=
    (eventually_contDiffAt_on_compact_of_locally_eventually_smooth hχc.isCompact hχΩ hlocal).mono
      (fun _ hk => contDiff_cutoff_perturbation_of_contDiffAt hχ hk)
  apply tendstoUniformlyOn_iteratedFDeriv_of_eventually_smooth isOpen_univ
    (fun x _ => ?_) (hs.mono fun _ hk => hk.contDiffOn)
    (hbound.cutoff_perturbation hlocal hχ hχΩ) m hK (subset_univ K)
  by_cases hx : x ∈ tsupport χ
  · simpa only [sub_self, smul_zero, add_zero, id_eq] using
      (((hpoint x (hχΩ hx)).sub_const x).const_smul (χ x)).const_add x
  · have hz : χ x = 0 := Function.notMem_support.mp (fun h => hx (subset_tsupport χ h))
    simpa only [hz, zero_smul, add_zero, id_eq] using
      (tendsto_const_nhds (x := x) (f := (atTop : Filter ℕ)))

theorem tendstoUniformlyOn_iteratedFDeriv_comp
    {d : ℕ} {U V : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hV : IsOpen V)
    {f g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {F G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G V) (hGU : MapsTo G V U)
    (hflocal : ∀ x ∈ U, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) W)
    (hglocal : ∀ x ∈ V, ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (g k) W)
    (hfjet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m F) atTop K)
    (hgjet : ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (g k)) (iteratedFDeriv ℝ m G) atTop K)
    (m : ℕ) {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) (hKV : K ⊆ V) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k ∘ g k))
      (iteratedFDeriv ℝ m (F ∘ G)) atTop K := by
  have hfconv := locallyUniformly_of_tendsto_zeroJet hU (hfjet 0)
  have hgconv := locallyUniformly_of_tendsto_zeroJet hV (hgjet 0)
  have hgc (C : Set (EuclideanSpace ℝ (Fin d))) (hC : IsCompact C) (hCV : C ⊆ V) :
      TendstoUniformlyOn g G atTop C :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hC).mp (hgconv.mono hCV)
  have hbound := (locallyEventuallyBoundedDerivatives_of_tendsto_jets hU hF hfjet).comp hU
    (locallyEventuallyBoundedDerivatives_of_tendsto_jets hV hG hgjet) hG.continuousOn hGU
    hgc hflocal hglocal
  have hpoint (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ V) :
      Tendsto (fun k => (f k ∘ g k) x) atTop (𝓝 ((F ∘ G) x)) :=
    hfconv.tendsto_comp (hF.continuousOn _ (hGU hx)) (hGU hx)
      (tendsto_nhdsWithin_iff.mpr ⟨hgconv.tendsto_at hx,
        (hgconv.tendsto_at hx).eventually (hU.mem_nhds (hGU hx))⟩)
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((tendstoLocallyUniformlyOn_iteratedFDeriv_of_locally_eventually_smooth hpoint
      (locally_eventually_smooth_comp hU hV hG.continuousOn hGU hgc hflocal hglocal)
      hbound m).mono hKV)

theorem finite_composition_tendsto_smoothly_id
    {d : ℕ} {ι : Type*}
    (a : ι → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : List ι)
    (hsmooth : ∀ i ∈ L, ∀ᶠ k in atTop, ContDiff ℝ ∞ (a i k))
    (hjet : ∀ i ∈ L, ∀ m K, IsCompact K → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (a i k)) (iteratedFDeriv ℝ m id) atTop K) :
    (∀ᶠ k in atTop, ContDiff ℝ ∞ (L.foldr (fun i b => a i k ∘ b) id)) ∧
      ∀ m K, IsCompact K → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (L.foldr (fun i b => a i k ∘ b) id))
        (iteratedFDeriv ℝ m id) atTop K := by
  induction L with
  | nil =>
    refine ⟨Eventually.of_forall (fun _ => contDiff_id), ?_⟩
    intro m K _
    exact Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
      Eventually.of_forall (fun _ _ _ => by simpa only [List.foldr_nil, dist_self] using hε)
  | cons i L ih =>
    obtain ⟨hLs, hLj⟩ := ih (fun j hj => hsmooth j (List.mem_cons_of_mem i hj))
      (fun j hj => hjet j (List.mem_cons_of_mem i hj))
    have his := hsmooth i (List.mem_cons_self)
    refine ⟨?_, ?_⟩
    · filter_upwards [his, hLs] with k hk hLk
      exact hk.comp hLk
    · intro m K hK
      simpa only [List.foldr_cons, Function.id_comp] using
        tendstoUniformlyOn_iteratedFDeriv_comp isOpen_univ isOpen_univ
          contDiff_id.contDiffOn contDiff_id.contDiffOn (mapsTo_univ _ _)
          (fun x _ => ⟨univ, isOpen_univ, mem_univ x, his.mono fun _ hk => hk.contDiffOn⟩)
          (fun x _ => ⟨univ, isOpen_univ, mem_univ x, hLs.mono fun _ hk => hk.contDiffOn⟩)
          (fun m K hK _ => hjet i List.mem_cons_self m K hK)
          (fun m K hK _ => hLj m K hK) m hK (subset_univ K)



theorem tendstoUniformlyOn_comp_jet
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {f : ℕ → EuclideanSpace ℝ (Fin d) → E}
    {g : ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {F : EuclideanSpace ℝ (Fin d) → E}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hsf : ∀ᶠ k in atTop, ContDiff ℝ ∞ (f k))
    (hsg : ∀ᶠ k in atTop, ContDiff ℝ ∞ (g k))
    (hf : ∀ m K, IsCompact K → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k)) (iteratedFDeriv ℝ m F) atTop K)
    (hg : ∀ m K, IsCompact K → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (g k)) (iteratedFDeriv ℝ m G) atTop K)
    (m : ℕ) {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k ∘ g k))
      (iteratedFDeriv ℝ m (F ∘ G)) atTop K := by
  have hfzero := locallyUniformly_of_tendsto_zeroJet isOpen_univ
    (fun C hC _ => hf 0 C hC)
  have hgzero := locallyUniformly_of_tendsto_zeroJet isOpen_univ
    (fun C hC _ => hg 0 C hC)
  have hfb := locallyEventuallyBoundedDerivatives_of_tendsto_jets isOpen_univ
    hF.contDiffOn (fun l C hC _ => hf l C hC)
  have hgb := locallyEventuallyBoundedDerivatives_of_tendsto_jets isOpen_univ
    hG.contDiffOn (fun l C hC _ => hg l C hC)
  apply tendstoUniformlyOn_iteratedFDeriv_of_eventually_smooth isOpen_univ
    (fun x _ => ?_) ((hsf.and hsg).mono fun _ hk => (hk.1.comp hk.2).contDiffOn)
    (hfb.comp_univ hgb hsf hsg) m hK (subset_univ K)
  exact hfzero.tendsto_comp hF.continuous.continuousWithinAt (mem_univ _)
    (by simpa only [nhdsWithin_univ] using hgzero.tendsto_at (mem_univ x))

theorem tendstoUniformlyOn_finite_comp_jet
    {ι : Type*} {d : ℕ}
    (a : ι → ℕ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (l : List ι)
    (hs : ∀ i ∈ l, ∀ᶠ k in atTop, ContDiff ℝ ∞ (a i k))
    (ha : ∀ i ∈ l, ∀ m K, IsCompact K → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (a i k)) (iteratedFDeriv ℝ m id) atTop K) :
    (∀ᶠ k in atTop, ContDiff ℝ ∞ (l.foldr (fun i f => a i k ∘ f) id)) ∧
      ∀ m K, IsCompact K → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m (l.foldr (fun i f => a i k ∘ f) id))
        (iteratedFDeriv ℝ m id) atTop K := by
  exact finite_composition_tendsto_smoothly_id a l hs ha

end Poincare.Analysis.Calculus
