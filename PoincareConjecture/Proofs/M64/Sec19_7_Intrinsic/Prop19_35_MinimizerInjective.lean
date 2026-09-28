import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConstrainedMinimizer
import Mathlib.Topology.Piecewise













noncomputable section
set_option autoImplicit false

open Set
open scoped Topology ENNReal NNReal

namespace PoincareConjecture




theorem m64Intrinsic_variation_rescale
    {X : Type*} [PseudoEMetricSpace X] (γ : ℝ → X) {L : ℝ} (hL : 0 ≤ L) :
    eVariationOn (fun t => γ (L * t)) (Icc 0 1) = eVariationOn γ (Icc 0 L) := by
  have hmono : MonotoneOn (fun t : ℝ => L * t) (Icc 0 1) :=
    fun _ _ _ _ h => mul_le_mul_of_nonneg_left h hL
  have himage : (fun t : ℝ => L * t) '' Icc 0 1 = Icc 0 L := by
    simpa using (continuous_const.mul continuous_id).continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1) hmono
  change eVariationOn (γ ∘ fun t => L * t) (Icc 0 1) = _
  rw [eVariationOn.comp_eq_of_monotoneOn γ _ hmono, himage]





theorem m64Intrinsic_unit_speed_constrained_minimizer_injOn
    {X : Type*} [MetricSpace X] {K : Set X} {γ : ℝ → X} {L : ℝ}
    (hL : 0 ≤ L) (hc : ContinuousOn γ (Icc 0 L))
    (hunit : HasUnitSpeedOn γ (Icc 0 L)) (hconf : MapsTo γ (Icc 0 L) K)
    (hmin : ∀ τ : ℝ → X, ContinuousOn τ (Icc 0 1) →
      τ 0 = γ 0 → τ 1 = γ L → MapsTo τ (Icc 0 1) K →
      ENNReal.ofReal L ≤ eVariationOn τ (Icc 0 1)) : InjOn γ (Icc 0 L) := by
  classical
  intro a ha b hb heq
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha heq.symm (le_of_not_ge hab)).symm
  by_contra hne
  have hab' : a < b := lt_of_le_of_ne hab hne
  let σ : ℝ → X := (Icc a b).piecewise (fun _ => γ a) γ
  have hleft : EqOn σ γ (Icc 0 a) := by
    intro t ht
    by_cases h : t ∈ Icc a b
    · have hta : t = a := le_antisymm ht.2 h.1
      simp [σ, hta, hab]
    · simp [σ, h]
  have hmiddle : EqOn σ (fun _ => γ a) (Icc a b) := by
    intro t ht
    simp [σ, ht]
  have hright : EqOn σ γ (Icc b L) := by
    intro t ht
    by_cases h : t ∈ Icc a b
    · have htb : t = b := le_antisymm h.2 ht.1
      simp [σ, htb, hab, heq]
    · simp [σ, h]
  have hσc : ContinuousOn σ (Icc 0 L) := by
    apply ContinuousOn.piecewise _ continuousOn_const (hc.mono inter_subset_left)
    intro t ht
    have ht' := ht.2
    rw [frontier_Icc hab, mem_insert_iff, mem_singleton_iff] at ht'
    rcases ht' with rfl | rfl
    · rfl
    · exact heq
  have hσconf : MapsTo σ (Icc 0 L) K := by
    intro t ht
    by_cases h : t ∈ Icc a b
    · simpa [σ, h] using hconf ha
    · simpa [σ, h] using hconf ht
  have hva : eVariationOn σ (Icc 0 a) = ENNReal.ofReal a := by
    rw [eVariationOn.eq_of_eqOn hleft]
    have h := hunit (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL⟩) ha
    have hi : Icc 0 L ∩ Icc 0 a = Icc 0 a :=
      inter_eq_right.mpr (Icc_subset_Icc le_rfl ha.2)
    simpa only [hi, NNReal.coe_one, one_mul, sub_zero] using h
  have hvab : eVariationOn σ (Icc a b) = 0 := by
    rw [eVariationOn.eq_of_eqOn hmiddle]
    apply eVariationOn.constant_on
    rintro _ ⟨s, _, rfl⟩ _ ⟨t, _, rfl⟩
    rfl
  have hvb : eVariationOn σ (Icc b L) = ENNReal.ofReal (L - b) := by
    rw [eVariationOn.eq_of_eqOn hright]
    have h := hunit hb (show L ∈ Icc 0 L from ⟨hL, le_rfl⟩)
    have hi : Icc 0 L ∩ Icc b L = Icc b L :=
      inter_eq_right.mpr (Icc_subset_Icc hb.1 le_rfl)
    simpa only [hi, NNReal.coe_one, one_mul] using h
  have hv0b : eVariationOn σ (Icc 0 b) = ENNReal.ofReal a := by
    have h := eVariationOn.Icc_add_Icc σ (s := univ) ha.1 hab (mem_univ a)
    simpa only [univ_inter, hva, hvab, add_zero] using h.symm
  have hvσ : eVariationOn σ (Icc 0 L) = ENNReal.ofReal (a + (L - b)) := by
    have h := eVariationOn.Icc_add_Icc σ (s := univ) hb.1 hb.2 (mem_univ b)
    rw [univ_inter, univ_inter, univ_inter, hv0b, hvb,
      ← ENNReal.ofReal_add ha.1 (sub_nonneg.mpr hb.2)] at h
    exact h.symm
  have hscale : MapsTo (fun t : ℝ => L * t) (Icc 0 1) (Icc 0 L) := by
    intro t ht
    exact ⟨mul_nonneg hL ht.1, by simpa using mul_le_mul_of_nonneg_left ht.2 hL⟩
  have hmin' := hmin (fun t => σ (L * t))
    (hσc.comp (continuous_const.mul continuous_id).continuousOn hscale)
    (by simpa only [mul_zero] using hleft ⟨le_rfl, ha.1⟩)
    (by simpa only [mul_one] using hright ⟨hb.2, le_rfl⟩)
    (hσconf.comp hscale)
  rw [m64Intrinsic_variation_rescale σ hL, hvσ] at hmin'
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg ha.1 (sub_nonneg.mpr hb.2))).mp hmin'
  linarith





theorem m64Intrinsic_exists_embedded_constrained_minimizer
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    {z y : X} {σ : ℝ → X}
    (hc : ContinuousOn σ (Icc 0 1)) (h0 : σ 0 = z) (h1 : σ 1 = y)
    (hconf : MapsTo σ (Icc 0 1) K)
    (hv : BoundedVariationOn σ (Icc 0 1)) :
    ∃ (η : ℝ → X) (L : ℝ), 0 ≤ L ∧ η 0 = z ∧ η L = y ∧
      MapsTo η (Icc 0 L) K ∧ HasUnitSpeedOn η (Icc 0 L) ∧
      LipschitzOnWith 1 η (Icc 0 L) ∧ InjOn η (Icc 0 L) ∧
      (∀ τ : ℝ → X, ContinuousOn τ (Icc 0 1) → τ 0 = z → τ 1 = y →
        MapsTo τ (Icc 0 1) K → ENNReal.ofReal L ≤ eVariationOn τ (Icc 0 1)) := by
  obtain ⟨η, L, hL, hη0, hη1, hηconf, hηunit, hηlip, _, hηmin⟩ :=
    m64Intrinsic_exists_unit_speed_constrained_minimizer hK hc h0 h1 hconf hv
  refine ⟨η, L, hL, hη0, hη1, hηconf, hηunit, hηlip, ?_, hηmin⟩
  apply m64Intrinsic_unit_speed_constrained_minimizer_injOn hL
    hηlip.continuousOn hηunit hηconf
  simpa only [hη0, hη1] using hηmin

end PoincareConjecture
