import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MinimizerInjective

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology ENNReal NNReal

namespace PoincareConjecture

theorem m64Intrinsic_subarc_replacement
    {X : Type*} [MetricSpace X] {K : Set X} {γ τ : ℝ → X} {L a b : ℝ}
    (hL : 0 ≤ L) (ha : a ∈ Icc 0 L) (hb : b ∈ Icc 0 L) (hab : a ≤ b)
    (hc : ContinuousOn γ (Icc 0 L)) (hunit : HasUnitSpeedOn γ (Icc 0 L))
    (hconf : MapsTo γ (Icc 0 L) K) (hτc : ContinuousOn τ (Icc a b))
    (hτa : τ a = γ a) (hτb : τ b = γ b) (hτconf : MapsTo τ (Icc a b) K) :
    ∃ σ : ℝ → X, ContinuousOn σ (Icc 0 L) ∧ σ 0 = γ 0 ∧ σ L = γ L ∧
      MapsTo σ (Icc 0 L) K ∧
      eVariationOn σ (Icc 0 L) =
        ENNReal.ofReal a + eVariationOn τ (Icc a b) + ENNReal.ofReal (L - b) := by
  classical
  let σ : ℝ → X := (Icc a b).piecewise τ γ
  have hleft : EqOn σ γ (Icc 0 a) := by
    intro t ht
    by_cases h : t ∈ Icc a b
    · have hta : t = a := le_antisymm ht.2 h.1
      simp [σ, hta, hab, hτa]
    · simp [σ, h]
  have hmiddle : EqOn σ τ (Icc a b) := by
    intro t ht
    simp [σ, ht]
  have hright : EqOn σ γ (Icc b L) := by
    intro t ht
    by_cases h : t ∈ Icc a b
    · have htb : t = b := le_antisymm h.2 ht.1
      simp [σ, htb, hab, hτb]
    · simp [σ, h]
  have hσc : ContinuousOn σ (Icc 0 L) := by
    apply ContinuousOn.piecewise _ _ (hc.mono inter_subset_left)
    · intro t ht
      have ht' := ht.2
      rw [frontier_Icc hab, mem_insert_iff, mem_singleton_iff] at ht'
      rcases ht' with rfl | rfl
      · exact hτa
      · exact hτb
    · simpa only [isClosed_Icc.closure_eq] using hτc.mono
        (inter_subset_right : Icc 0 L ∩ Icc a b ⊆ Icc a b)
  refine ⟨σ, hσc, hleft ⟨le_rfl, ha.1⟩, hright ⟨hb.2, le_rfl⟩, ?_, ?_⟩
  · intro t ht
    by_cases h : t ∈ Icc a b
    · simpa [σ, h] using hτconf h
    · simpa [σ, h] using hconf ht
  · have hva : eVariationOn σ (Icc 0 a) = ENNReal.ofReal a := by
      rw [eVariationOn.eq_of_eqOn hleft]
      have h := hunit (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL⟩) ha
      have hi : Icc 0 L ∩ Icc 0 a = Icc 0 a :=
        inter_eq_right.mpr (Icc_subset_Icc le_rfl ha.2)
      simpa only [hi, NNReal.coe_one, one_mul, sub_zero] using h
    have hvb : eVariationOn σ (Icc b L) = ENNReal.ofReal (L - b) := by
      rw [eVariationOn.eq_of_eqOn hright]
      have h := hunit hb (show L ∈ Icc 0 L from ⟨hL, le_rfl⟩)
      have hi : Icc 0 L ∩ Icc b L = Icc b L :=
        inter_eq_right.mpr (Icc_subset_Icc hb.1 le_rfl)
      simpa only [hi, NNReal.coe_one, one_mul] using h
    have hfirst := eVariationOn.Icc_add_Icc σ (s := univ) ha.1 hab (mem_univ a)
    have hsecond := eVariationOn.Icc_add_Icc σ (s := univ) hb.1 hb.2 (mem_univ b)
    simp only [univ_inter, hva, eVariationOn.eq_of_eqOn hmiddle] at hfirst
    simpa only [univ_inter, ← hfirst, hvb] using hsecond.symm

theorem m64Intrinsic_constrained_minimizer_subarc
    {X : Type*} [MetricSpace X] {K : Set X} {γ : ℝ → X} {L : ℝ}
    (hL : 0 ≤ L) (hc : ContinuousOn γ (Icc 0 L))
    (hunit : HasUnitSpeedOn γ (Icc 0 L)) (hconf : MapsTo γ (Icc 0 L) K)
    (hmin : ∀ τ : ℝ → X, ContinuousOn τ (Icc 0 1) →
      τ 0 = γ 0 → τ 1 = γ L → MapsTo τ (Icc 0 1) K →
      ENNReal.ofReal L ≤ eVariationOn τ (Icc 0 1))
    {a b : ℝ} (ha : a ∈ Icc 0 L) (hb : b ∈ Icc 0 L) (hab : a ≤ b)
    {τ : ℝ → X} (hτc : ContinuousOn τ (Icc a b))
    (hτa : τ a = γ a) (hτb : τ b = γ b) (hτconf : MapsTo τ (Icc a b) K) :
    ENNReal.ofReal (b - a) ≤ eVariationOn τ (Icc a b) := by
  obtain ⟨σ, hσc, hσ0, hσL, hσconf, hσvar⟩ :=
    m64Intrinsic_subarc_replacement hL ha hb hab hc hunit hconf hτc hτa hτb hτconf
  have hscale : MapsTo (fun t : ℝ => L * t) (Icc 0 1) (Icc 0 L) := by
    intro t ht
    exact ⟨mul_nonneg hL ht.1, by simpa using mul_le_mul_of_nonneg_left ht.2 hL⟩
  have hmin' := hmin (fun t => σ (L * t))
    (hσc.comp (continuous_const.mul continuous_id).continuousOn hscale)
    (by simpa only [mul_zero] using hσ0) (by simpa only [mul_one] using hσL)
    (hσconf.comp hscale)
  rw [m64Intrinsic_variation_rescale σ hL, hσvar] at hmin'
  have hsplit : ENNReal.ofReal L = ENNReal.ofReal a +
      ENNReal.ofReal (b - a) + ENNReal.ofReal (L - b) := by
    rw [← ENNReal.ofReal_add ha.1 (sub_nonneg.mpr hab),
      ← ENNReal.ofReal_add (by linarith [hb.1]) (sub_nonneg.mpr hb.2)]
    congr 1
    ring
  rw [hsplit, ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top,
    ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top] at hmin'
  exact hmin'

theorem m64Intrinsic_constrained_minimizer_subarc_unitInterval
    {X : Type*} [MetricSpace X] {K : Set X} {γ : ℝ → X} {L : ℝ}
    (hL : 0 ≤ L) (hc : ContinuousOn γ (Icc 0 L))
    (hunit : HasUnitSpeedOn γ (Icc 0 L)) (hconf : MapsTo γ (Icc 0 L) K)
    (hmin : ∀ τ : ℝ → X, ContinuousOn τ (Icc 0 1) →
      τ 0 = γ 0 → τ 1 = γ L → MapsTo τ (Icc 0 1) K →
      ENNReal.ofReal L ≤ eVariationOn τ (Icc 0 1))
    {a b : ℝ} (ha : a ∈ Icc 0 L) (hb : b ∈ Icc 0 L) (hab : a ≤ b)
    {τ : ℝ → X} (hτc : ContinuousOn τ (Icc 0 1))
    (hτa : τ 0 = γ a) (hτb : τ 1 = γ b) (hτconf : MapsTo τ (Icc 0 1) K) :
    ENNReal.ofReal (b - a) ≤ eVariationOn τ (Icc 0 1) := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  have hd : 0 < b - a := sub_pos.mpr hab'
  let f : ℝ → ℝ := fun t => (t - a) / (b - a)
  have hfc : Continuous f := (continuous_id.sub continuous_const).div_const _
  have hfm : MonotoneOn f (Icc a b) := by
    intro s _ t _ hst
    exact div_le_div_of_nonneg_right (sub_le_sub_right hst a) hd.le
  have hf0 : f a = 0 := by simp [f]
  have hf1 : f b = 1 := by simp [f, hd.ne']
  have hfimage : f '' Icc a b = Icc 0 1 := by
    simpa only [hf0, hf1] using hfc.continuousOn.image_Icc_of_monotoneOn hab hfm
  have hfmap : MapsTo f (Icc a b) (Icc 0 1) := by
    rw [← hfimage]
    exact mapsTo_image _ _
  have h := m64Intrinsic_constrained_minimizer_subarc hL hc hunit hconf hmin ha hb hab
    (hτc.comp hfc.continuousOn hfmap) (by simpa only [Function.comp_apply, hf0] using hτa)
    (by simpa only [Function.comp_apply, hf1] using hτb) (hτconf.comp hfmap)
  change ENNReal.ofReal (b - a) ≤ eVariationOn (τ ∘ f) (Icc a b) at h
  rwa [eVariationOn.comp_eq_of_monotoneOn τ f hfm, hfimage] at h

end PoincareConjecture
