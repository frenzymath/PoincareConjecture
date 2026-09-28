import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Uniqueness.Open

noncomputable section

namespace Poincare.ODE.LocalFlow

open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem glue_smooth_solution_families
    {F : E → E} {U V : Set E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hV : IsOpen V) {J₁ J₂ : Set ℝ}
    (hJ₁ : IsOpen J₁) (hJ₂ : IsOpen J₂) (hc₁ : Convex ℝ J₁) (hc₂ : Convex ℝ J₂)
    {Φ₁ Φ₂ : E × ℝ → E}
    (hs₁ : ContDiffOn ℝ ∞ Φ₁ (V ×ˢ J₁))
    (hs₂ : ContDiffOn ℝ ∞ Φ₂ (V ×ˢ J₂))
    (hd₁ : ∀ y ∈ V, ∀ t ∈ J₁, Φ₁ (y, t) ∈ U ∧
      HasDerivAt (fun s => Φ₁ (y, s)) (F (Φ₁ (y, t))) t)
    (hd₂ : ∀ y ∈ V, ∀ t ∈ J₂, Φ₂ (y, t) ∈ U ∧
      HasDerivAt (fun s => Φ₂ (y, s)) (F (Φ₂ (y, t))) t)
    {c : ℝ} (hc : c ∈ J₁ ∩ J₂) (hjoin : ∀ y ∈ V, Φ₁ (y, c) = Φ₂ (y, c)) :
    ∃ Φ : E × ℝ → E,
      ContDiffOn ℝ ∞ Φ (V ×ˢ (J₁ ∪ J₂)) ∧
      EqOn Φ Φ₁ (V ×ˢ J₁) ∧ EqOn Φ Φ₂ (V ×ˢ J₂) ∧
      ∀ y ∈ V, ∀ t ∈ J₁ ∪ J₂, Φ (y, t) ∈ U ∧
        HasDerivAt (fun s => Φ (y, s)) (F (Φ (y, t))) t := by
  classical
  have heq : ∀ y ∈ V, EqOn (fun t => Φ₁ (y, t)) (fun t => Φ₂ (y, t)) (J₁ ∩ J₂) := by
    intro y hy
    exact Poincare.ODE.eqOn_of_hasDerivAt hU hF (hJ₁.inter hJ₂)
      (hc₁.inter hc₂).isPreconnected (fun t ht => hd₁ y hy t ht.1)
      (fun t ht => hd₂ y hy t ht.2) hc (hjoin y hy)
  let Φ : E × ℝ → E := fun p => if p.2 ∈ J₁ then Φ₁ p else Φ₂ p
  have heq₁ : EqOn Φ Φ₁ (V ×ˢ J₁) := fun p hp => if_pos hp.2
  have heq₂ : EqOn Φ Φ₂ (V ×ˢ J₂) := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    by_cases ht₁ : t ∈ J₁
    · exact (if_pos ht₁).trans (heq y hy ⟨ht₁, ht⟩)
    · exact if_neg ht₁
  have hgerm₁ {p : E × ℝ} (hp : p ∈ V ×ˢ J₁) : Φ =ᶠ[𝓝 p] Φ₁ :=
    Filter.Eventually.mono ((hV.prod hJ₁).mem_nhds hp) fun q hq => heq₁ hq
  have hgerm₂ {p : E × ℝ} (hp : p ∈ V ×ˢ J₂) : Φ =ᶠ[𝓝 p] Φ₂ :=
    Filter.Eventually.mono ((hV.prod hJ₂).mem_nhds hp) fun q hq => heq₂ hq
  refine ⟨Φ, ?_, heq₁, heq₂, ?_⟩
  · rintro ⟨y, t⟩ ⟨hy, ht | ht⟩
    · exact ((hs₁.contDiffAt ((hV.prod hJ₁).mem_nhds ⟨hy, ht⟩)).congr_of_eventuallyEq
        (hgerm₁ ⟨hy, ht⟩)).contDiffWithinAt
    · exact ((hs₂.contDiffAt ((hV.prod hJ₂).mem_nhds ⟨hy, ht⟩)).congr_of_eventuallyEq
        (hgerm₂ ⟨hy, ht⟩)).contDiffWithinAt
  · intro y hy t ht
    rcases ht with ht | ht
    · have he : (fun s => Φ (y, s)) =ᶠ[𝓝 t] (fun s => Φ₁ (y, s)) :=
        Filter.Eventually.mono (hJ₁.mem_nhds ht) fun s hs => heq₁ ⟨hy, hs⟩
      rw [heq₁ (show (y, t) ∈ V ×ˢ J₁ from ⟨hy, ht⟩)]
      exact ⟨(hd₁ y hy t ht).1, (hd₁ y hy t ht).2.congr_of_eventuallyEq he⟩
    · have he : (fun s => Φ (y, s)) =ᶠ[𝓝 t] (fun s => Φ₂ (y, s)) :=
        Filter.Eventually.mono (hJ₂.mem_nhds ht) fun s hs => heq₂ ⟨hy, hs⟩
      rw [heq₂ (show (y, t) ∈ V ×ˢ J₂ from ⟨hy, ht⟩)]
      exact ⟨(hd₂ y hy t ht).1, (hd₂ y hy t ht).2.congr_of_eventuallyEq he⟩

variable [FiniteDimensional ℝ E]

theorem exists_uniform_smooth_local_flows
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {F : E → E} (hF : ContDiffOn ℝ ∞ F U) :
    ∃ δ > 0, ∀ x ∈ K, ∃ (V : Set E) (Φ : E × ℝ → E),
      IsOpen V ∧ x ∈ V ∧ ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (-δ) δ) ∧
      (∀ y ∈ V, Φ (y, 0) = y) ∧
      ∀ y ∈ V, ∀ t ∈ Ioo (-δ) δ, Φ (y, t) ∈ U ∧
        HasDerivAt (fun s => Φ (y, s)) (F (Φ (y, t))) t := by
  let P : Set E → Prop := fun S =>
    ∃ δ > 0, ∀ x ∈ S, ∃ (V : Set E) (Φ : E × ℝ → E),
      IsOpen V ∧ x ∈ V ∧ ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (-δ) δ) ∧
      (∀ y ∈ V, Φ (y, 0) = y) ∧
      ∀ y ∈ V, ∀ t ∈ Ioo (-δ) δ, Φ (y, t) ∈ U ∧
        HasDerivAt (fun s => Φ (y, s)) (F (Φ (y, t))) t
  change P K
  refine hK.induction_on (p := P) ?_ ?_ ?_ ?_
  · exact ⟨1, zero_lt_one, fun _ hx => False.elim hx⟩
  · rintro S T hST ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, fun x hx => h x (hST hx)⟩
  · rintro S T ⟨δ, hδ, hS⟩ ⟨ε, hε, hT⟩
    have hleft : Ioo (-(min δ ε)) (min δ ε) ⊆ Ioo (-δ) δ :=
      Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
    have hright : Ioo (-(min δ ε)) (min δ ε) ⊆ Ioo (-ε) ε :=
      Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨V, Φ, hV, hxV, hs, hi, hd⟩ := hS x hx
      exact ⟨V, Φ, hV, hxV, hs.mono (prod_mono_right hleft), hi,
        fun y hy t ht => hd y hy t (hleft ht)⟩
    · obtain ⟨V, Φ, hV, hxV, hs, hi, hd⟩ := hT x hx
      exact ⟨V, Φ, hV, hxV, hs.mono (prod_mono_right hright), hi,
        fun y hy t ht => hd y hy t (hright ht)⟩
  · intro x hx
    obtain ⟨V, δ, Φ, hV, hxV, _, hδ, hs, hi, hm, hd⟩ :=
      exists_smooth_localFlow hU hF (hKU hx)
    refine ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), δ, hδ, ?_⟩
    intro y hy
    exact ⟨V, Φ, hV, hy, hs, hi, fun z hz t ht => ⟨hm z hz t ht, hd z hz t ht⟩⟩

theorem exists_smooth_flow_along_compact_interval
    {F : E → E} {U : Set E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {γ : ℝ → E} {J : Set ℝ} (hJ : IsOpen J) (hcJ : Convex ℝ J)
    (hγ : ∀ t ∈ J, γ t ∈ U ∧ HasDerivAt γ (F (γ t)) t)
    {T : ℝ} (hT : 0 ≤ T) (hsub : Icc 0 T ⊆ J) :
    ∃ (V : Set E) (ε : ℝ) (Φ : E × ℝ → E), IsOpen V ∧ γ 0 ∈ V ∧ 0 < ε ∧
      ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (-ε) (T + ε)) ∧
      (∀ y ∈ V, Φ (y, 0) = y) ∧
      ∀ y ∈ V, ∀ t ∈ Ioo (-ε) (T + ε), Φ (y, t) ∈ U ∧
        HasDerivAt (fun s => Φ (y, s)) (F (Φ (y, t))) t := by
  have hcompact : IsCompact (γ '' Icc 0 T) :=
    isCompact_Icc.image_of_continuousOn
      (fun t ht => (hγ t (hsub ht)).2.continuousAt.continuousWithinAt)
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_smooth_local_flows hU hcompact
    (fun _ ⟨t, ht, he⟩ => he ▸ (hγ t (hsub ht)).1) hF
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hT hδ.le) hN
  let d : ℝ := T / N
  let s : ℕ → ℝ := fun i => i * d
  have hd : 0 ≤ d := div_nonneg hT hNpos.le
  have hsmall : d < δ := by
    apply (div_lt_iff₀ hNpos).2
    have := (div_lt_iff₀ hδ).mp hN
    nlinarith
  have hs0 : s 0 = 0 := by simp [s]
  have hsN : s N = T := by dsimp [s, d]; field_simp
  have hsnonneg (i : ℕ) : 0 ≤ s i := mul_nonneg (Nat.cast_nonneg i) hd
  have hsstep (i : ℕ) : s (i + 1) = s i + d := by dsimp [s]; push_cast; ring
  have hsle (i : ℕ) (hi : i ≤ N) : s i ≤ T := by
    rw [← hsN]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hd
  have aux : ∀ i, i ≤ N → ∃ (V : Set E) (ε : ℝ) (Φ : E × ℝ → E),
      IsOpen V ∧ γ 0 ∈ V ∧ 0 < ε ∧
      ContDiffOn ℝ ∞ Φ (V ×ˢ Ioo (-ε) (s i + ε)) ∧
      (∀ y ∈ V, Φ (y, 0) = y) ∧ Φ (γ 0, s i) = γ (s i) ∧
      ∀ y ∈ V, ∀ t ∈ Ioo (-ε) (s i + ε), Φ (y, t) ∈ U ∧
        HasDerivAt (fun r => Φ (y, r)) (F (Φ (y, t))) t := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨V, Φ, hV, hxV, hs, hi, hflow⟩ :=
        hlocal (γ 0) (mem_image_of_mem γ ⟨le_rfl, hT⟩)
      refine ⟨V, δ, Φ, hV, hxV, hδ, ?_, hi, ?_, ?_⟩
      · simpa only [hs0, zero_add] using hs
      · simpa only [hs0] using hi (γ 0) hxV
      · simpa only [hs0, zero_add] using hflow
    | succ i ih =>
      intro hi
      obtain ⟨V, ε, Φ, hV, hxV, hε, hsΦ, hinit, hend, hflow⟩ :=
        ih (Nat.le_of_succ_le hi)
      have hiT : s i ∈ Icc 0 T := ⟨hsnonneg i, hsle i (Nat.le_of_succ_le hi)⟩
      have hnT : s (i + 1) ∈ Icc 0 T := ⟨hsnonneg _, hsle _ hi⟩
      obtain ⟨W, Ψ, hW, hxW, hsΨ, hinitΨ, hflowΨ⟩ :=
        hlocal (γ (s i)) (mem_image_of_mem γ hiT)
      have hiold : s i ∈ Ioo (-ε) (s i + ε) := ⟨by linarith [hsnonneg i], by linarith⟩
      let B : E → E := fun y => Φ (y, s i)
      have hsB : ContDiffOn ℝ ∞ B V := hsΦ.comp
        (contDiff_id.prodMk contDiff_const).contDiffOn (fun y hy => ⟨hy, hiold⟩)
      let V' : Set E := V ∩ B ⁻¹' W
      have hV' : IsOpen V' := hsB.continuousOn.isOpen_inter_preimage hV hW
      have hxV' : γ 0 ∈ V' := ⟨hxV, by
        change Φ (γ 0, s i) ∈ W
        rwa [hend]⟩
      let J₂ : Set ℝ := Ioo (s i - δ) (s i + δ)
      let Ψ' : E × ℝ → E := fun p => Ψ (B p.1, p.2 - s i)
      have htime (t : ℝ) (ht : t ∈ J₂) : t - s i ∈ Ioo (-δ) δ :=
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hsΨ' : ContDiffOn ℝ ∞ Ψ' (V' ×ˢ J₂) := by
        apply hsΨ.comp
        · exact ((hsB.mono inter_subset_left).comp contDiffOn_fst (fun _ hp => hp.1)).prodMk
            (contDiffOn_snd.sub contDiffOn_const)
        · intro p hp
          exact ⟨hp.1.2, htime p.2 hp.2⟩
      have hflowΨ' : ∀ y ∈ V', ∀ t ∈ J₂, Ψ' (y, t) ∈ U ∧
          HasDerivAt (fun r => Ψ' (y, r)) (F (Ψ' (y, t))) t := by
        intro y hy t ht
        refine ⟨(hflowΨ (B y) hy.2 _ (htime t ht)).1, ?_⟩
        simpa [Ψ', Function.comp_def] using
          (hflowΨ (B y) hy.2 _ (htime t ht)).2.scomp t ((hasDerivAt_id t).sub_const (s i))
      have hicommon : s i ∈ Ioo (-ε) (s i + ε) ∩ J₂ :=
        ⟨hiold, by constructor <;> linarith⟩
      obtain ⟨Ξ, hsΞ, heqΦ, heqΨ, hflowΞ⟩ := glue_smooth_solution_families hU hF hV'
        isOpen_Ioo isOpen_Ioo (convex_Ioo _ _) (convex_Ioo _ _)
        (hsΦ.mono (prod_mono_left inter_subset_left)) hsΨ'
        (fun y hy => hflow y hy.1) hflowΨ' hicommon (fun y hy => by
          simpa only [Ψ', sub_self, B] using (hinitΨ (B y) hy.2).symm)
      let ε' : ℝ := min ε (δ - d) / 2
      have hε' : 0 < ε' := half_pos (lt_min hε (sub_pos.mpr hsmall))
      have hε'le : ε' ≤ ε :=
        (half_le_self (le_of_lt (lt_min hε (sub_pos.mpr hsmall)))).trans (min_le_left _ _)
      have hε'd : d + ε' < δ := by
        have := (half_lt_self (lt_min hε (sub_pos.mpr hsmall))).trans_le (min_le_right ε (δ - d))
        dsimp [ε']
        linarith
      have hJsub : Ioo (-ε') (s (i + 1) + ε') ⊆ Ioo (-ε) (s i + ε) ∪ J₂ := by
        intro t ht
        by_cases hto : t < s i + ε
        · exact Or.inl ⟨by linarith [ht.1], hto⟩
        · right
          rw [hsstep] at ht
          exact ⟨by linarith, by linarith [ht.2]⟩
      have h0old : (0 : ℝ) ∈ Ioo (-ε) (s i + ε) :=
        ⟨by linarith, by linarith [hsnonneg i]⟩
      have hnnew : s (i + 1) ∈ J₂ := by rw [hsstep]; constructor <;> linarith
      have heqref : Ψ' (γ 0, s (i + 1)) = γ (s (i + 1)) := by
        have he : EqOn (fun t => Ψ' (γ 0, t)) γ (J ∩ J₂) :=
          Poincare.ODE.eqOn_of_hasDerivAt hU hF (hJ.inter isOpen_Ioo)
            (hcJ.inter (convex_Ioo _ _)).isPreconnected
            (fun t ht => hflowΨ' (γ 0) hxV' t ht.2) (fun t ht => hγ t ht.1)
            ⟨hsub hiT, hicommon.2⟩ (by
              simpa only [Ψ', sub_self, B, hend] using hinitΨ (γ (s i)) hxW)
        exact he ⟨hsub hnT, hnnew⟩
      refine ⟨V', ε', Ξ, hV', hxV', hε', hsΞ.mono (prod_mono_right hJsub), ?_, ?_, ?_⟩
      · intro y hy
        exact (heqΦ (show (y, 0) ∈ V' ×ˢ Ioo (-ε) (s i + ε) from ⟨hy, h0old⟩)).trans
          (hinit y hy.1)
      · exact (heqΨ (show (γ 0, s (i + 1)) ∈ V' ×ˢ J₂ from ⟨hxV', hnnew⟩)).trans heqref
      · exact fun y hy t ht => hflowΞ y hy t (hJsub ht)
  obtain ⟨V, ε, Φ, hV, hxV, hε, hs, hi, _, hf⟩ := aux N le_rfl
  rw [hsN] at hs hf
  exact ⟨V, ε, Φ, hV, hxV, hε, hs, hi, hf⟩

end Poincare.ODE.LocalFlow
