import PoincareConjecture.Proofs.M07.Topology.MetricSpace.Curves.CompactMetricMinimizer
import Mathlib.Topology.Order.IsLUB













noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal NNReal

namespace PoincareConjecture






theorem m64Intrinsic_exists_compact_constrained_minimizer
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    {z y : X} {σ : ℝ → X}
    (hc : ContinuousOn σ (Icc 0 1)) (h0 : σ 0 = z) (h1 : σ 1 = y)
    (hconf : MapsTo σ (Icc 0 1) K)
    (hv : BoundedVariationOn σ (Icc 0 1)) :
    ∃ γ : ℝ → X, γ 0 = z ∧ γ 1 = y ∧ MapsTo γ (Icc 0 1) K ∧
      LipschitzOnWith (eVariationOn γ (Icc 0 1)).toNNReal γ (Icc 0 1) ∧
      BoundedVariationOn γ (Icc 0 1) ∧
      ∀ τ : ℝ → X, ContinuousOn τ (Icc 0 1) → τ 0 = z → τ 1 = y →
        MapsTo τ (Icc 0 1) K →
        eVariationOn γ (Icc 0 1) ≤ eVariationOn τ (Icc 0 1) := by
  classical
  let S : Set ℝ≥0∞ := {l | ∃ τ : ℝ → X,
    ContinuousOn τ (Icc 0 1) ∧ τ 0 = z ∧ τ 1 = y ∧
      MapsTo τ (Icc 0 1) K ∧ BoundedVariationOn τ (Icc 0 1) ∧
        eVariationOn τ (Icc 0 1) = l}
  have hS : S.Nonempty := ⟨_, σ, hc, h0, h1, hconf, hv, rfl⟩
  have hSbelow : BddBelow S := ⟨0, fun _ _ => bot_le⟩
  obtain ⟨l, hlanti, hlconv, hlS⟩ := exists_seq_tendsto_sInf hS hSbelow
  choose τ hτc hτ0 hτ1 hτconf hτv hτlength using hlS
  have hlfinite (n : ℕ) : l n ≠ ⊤ := by
    rw [← hτlength n]
    exact hτv n
  choose η hη0 hη1 hηimage hηlip using
    (fun n => Poincare.MetricCurves.exists_normalized_path (hτc n) (hτv n))
  have hηconf (n : ℕ) : MapsTo (η n) (Icc 0 1) K := by
    intro t ht
    obtain ⟨s, hs, heq⟩ := (hηimage n).subset (mem_image_of_mem (η n) ht)
    exact heq ▸ hτconf n hs
  have hηcommon (n : ℕ) : LipschitzOnWith (l 0).toNNReal (η n) (Icc 0 1) := by
    apply (hηlip n).weaken
    rw [hτlength n]
    exact ENNReal.toNNReal_mono (hlfinite 0) (hlanti (Nat.zero_le n))
  obtain ⟨φ, γ, hφ, hconv, hγlip, hγ0, hγ1, hγconf⟩ :=
    Poincare.MetricCurves.exists_confined_uniform_limit hK hηcommon
      (fun n => (hη0 n).trans (hτ0 n))
      (fun n => (hη1 n).trans (hτ1 n)) hηconf
  have hvar : eVariationOn γ (Icc 0 1) ≤ sInf S :=
    Poincare.MetricCurves.eVariationOn_le_of_tendsto_bounds hconv
      (fun n => (Poincare.MetricCurves.eVariationOn_le_of_lipschitzOnWith
        (hηlip (φ n))).trans (by
          rw [hτlength (φ n)]
          exact ENNReal.coe_toNNReal_le_self))
      (hlconv.comp hφ.tendsto_atTop)
  have hγv : BoundedVariationOn γ (Icc 0 1) :=
    ne_top_of_le_ne_top (hlfinite 0) (hvar.trans
      (sInf_le ⟨τ 0, hτc 0, hτ0 0, hτ1 0, hτconf 0, hτv 0, hτlength 0⟩))
  have hmin (τ' : ℝ → X) (hc' : ContinuousOn τ' (Icc 0 1))
      (h0' : τ' 0 = z) (h1' : τ' 1 = y) (hconf' : MapsTo τ' (Icc 0 1) K) :
      eVariationOn γ (Icc 0 1) ≤ eVariationOn τ' (Icc 0 1) := by
    by_cases hv' : BoundedVariationOn τ' (Icc 0 1)
    · exact hvar.trans (sInf_le ⟨τ', hc', h0', h1', hconf', hv', rfl⟩)
    · have htop : eVariationOn τ' (Icc 0 1) = ⊤ := by
        simpa only [BoundedVariationOn, not_not] using hv'
      rw [htop]
      exact le_top
  obtain ⟨ν, hν0, hν1, hνimage, hνlip⟩ :=
    Poincare.MetricCurves.exists_normalized_path hγlip.continuousOn hγv
  have hνconf : MapsTo ν (Icc 0 1) K := by
    intro t ht
    obtain ⟨s, hs, heq⟩ := hνimage.subset (mem_image_of_mem ν ht)
    exact heq ▸ hγconf hs
  have hνlength : eVariationOn ν (Icc 0 1) = eVariationOn γ (Icc 0 1) := by
    apply le_antisymm
    · exact (Poincare.MetricCurves.eVariationOn_le_of_lipschitzOnWith hνlip).trans
        ENNReal.coe_toNNReal_le_self
    · exact hmin ν hνlip.continuousOn (hν0.trans hγ0) (hν1.trans hγ1) hνconf
  refine ⟨ν, hν0.trans hγ0, hν1.trans hγ1, hνconf, ?_, ?_, ?_⟩
  · rw [hνlength]
    exact hνlip
  · change eVariationOn ν (Icc 0 1) ≠ ⊤
    rw [hνlength]
    exact hγv
  · intro τ' hc' h0' h1' hconf'
    rw [hνlength]
    exact hmin τ' hc' h0' h1' hconf'





theorem m64Intrinsic_exists_unit_speed_constrained_minimizer
    {X : Type*} [MetricSpace X] {K : Set X} (hK : IsCompact K)
    {z y : X} {σ : ℝ → X}
    (hc : ContinuousOn σ (Icc 0 1)) (h0 : σ 0 = z) (h1 : σ 1 = y)
    (hconf : MapsTo σ (Icc 0 1) K)
    (hv : BoundedVariationOn σ (Icc 0 1)) :
    ∃ (η : ℝ → X) (L : ℝ), 0 ≤ L ∧ η 0 = z ∧ η L = y ∧
      MapsTo η (Icc 0 L) K ∧ HasUnitSpeedOn η (Icc 0 L) ∧
      LipschitzOnWith 1 η (Icc 0 L) ∧
      eVariationOn η (Icc 0 L) = ENNReal.ofReal L ∧
      (∀ τ : ℝ → X, ContinuousOn τ (Icc 0 1) → τ 0 = z → τ 1 = y →
        MapsTo τ (Icc 0 1) K → ENNReal.ofReal L ≤ eVariationOn τ (Icc 0 1)) := by
  obtain ⟨γ, hγ0, hγ1, hγconf, hγlip, hγv, hγmin⟩ :=
    m64Intrinsic_exists_compact_constrained_minimizer hK hc h0 h1 hconf hv
  obtain ⟨η, hη0, hη1, hηimage, hηunit, hηlip⟩ :=
    Poincare.MetricCurves.exists_arcLength_representative (by norm_num : (0 : ℝ) ≤ 1)
      hγlip.continuousOn hγv
  let L := (eVariationOn γ (Icc 0 1)).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hunit : eVariationOn η (Icc 0 L) = ENNReal.ofReal L := by
    have h := hηunit (show (0 : ℝ) ∈ Icc 0 L from ⟨le_rfl, hL⟩)
      (show L ∈ Icc 0 L from ⟨hL, le_rfl⟩)
    simpa only [L, inter_self, NNReal.coe_one, one_mul, sub_zero] using h
  refine ⟨η, L, hL, hη0.trans hγ0, hη1.trans hγ1, ?_, hηunit, hηlip, hunit, ?_⟩
  · intro t ht
    obtain ⟨s, hs, heq⟩ := hηimage.subset (mem_image_of_mem η ht)
    exact heq ▸ hγconf hs
  · intro τ hc' h0' h1' hconf'
    rw [show ENNReal.ofReal L = eVariationOn γ (Icc 0 1) from
      ENNReal.ofReal_toReal hγv]
    exact hγmin τ hc' h0' h1' hconf'

end PoincareConjecture
