import Mathlib.Analysis.ConstantSpeed










set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace PoincareConjecture.M60



theorem lipschitzOnWith_of_constant_speed {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {s : Set ℝ} {C : ℝ≥0} (hf : HasConstantSpeedOnWith f s C) :
    LipschitzOnWith C f s := by
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa only [edist_comm] using this hy hx (le_of_not_ge hxy)
  calc
    edist (f x) (f y) ≤ eVariationOn f (s ∩ Icc x y) :=
      eVariationOn.edist_le f ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
    _ = ENNReal.ofReal (C * (y - x)) := hf hx hy
    _ = C * edist x y := by
      rw [edist_dist, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy),
        ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]




theorem lipschitzOnWith_variationOnFromTo {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {s : Set ℝ} {C : ℝ≥0} (hf : LipschitzOnWith C f s)
    {a : ℝ} (ha : a ∈ s) : LipschitzOnWith C (variationOnFromTo f s a) s := by
  have hloc := hf.locallyBoundedVariationOn
  have hmono := variationOnFromTo.monotoneOn hloc ha
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa only [edist_comm] using this hy hx (le_of_not_ge hxy)
  rw [edist_dist, Real.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr (hmono hx hy hxy)),
    variationOnFromTo.sub_right hloc ha hy hx,
    variationOnFromTo.eq_of_le f s hxy, ENNReal.ofReal_toReal (hloc x y hx hy)]
  calc
    eVariationOn f (s ∩ Icc x y) ≤ C * eVariationOn id (s ∩ Icc x y) := by
      simpa only [Function.comp_id] using
        hf.comp_eVariationOn_le (g := id) (fun _ hz => hz.1)
    _ ≤ C * eVariationOn id (Icc x y) := by
      gcongr
      exact eVariationOn.mono id inter_subset_right
    _ = C * edist x y := by
      rw [eVariationOn_id_Icc, edist_dist, Real.dist_eq, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr hxy)]




theorem lipschitzOnWith_naturalParameterization {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {s : Set ℝ} (hf : LocallyBoundedVariationOn f s)
    {a : ℝ} (ha : a ∈ s) :
    LipschitzOnWith 1 (naturalParameterization f s a) (variationOnFromTo f s a '' s) :=
  lipschitzOnWith_of_constant_speed (has_unit_speed_naturalParameterization f hf ha)




theorem exists_lipschitz_length_factorization {E : Type*} [EMetricSpace E]
    {f : ℝ → E} {s : Set ℝ} {C : ℝ≥0} (hf : LipschitzOnWith C f s)
    {a : ℝ} (ha : a ∈ s) :
    ∃ (ell : ℝ → ℝ) (beta : ℝ → E),
      ell a = 0 ∧ MonotoneOn ell s ∧ LipschitzOnWith C ell s ∧
      LipschitzOnWith 1 beta (ell '' s) ∧ ∀ x ∈ s, beta (ell x) = f x := by
  refine ⟨variationOnFromTo f s a, naturalParameterization f s a,
    variationOnFromTo.self f s a,
    variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn ha,
    lipschitzOnWith_variationOnFromTo hf ha,
    lipschitzOnWith_naturalParameterization hf.locallyBoundedVariationOn ha, ?_⟩
  intro x hx
  exact edist_eq_zero.mp (edist_naturalParameterization_eq_zero hf.locallyBoundedVariationOn ha hx)




theorem lipschitzOnWith_reparameterized_length {E : Type*} [PseudoEMetricSpace E]
    {f : ℝ → E} {s : Set ℝ} {phi : ℝ → ℝ} (hphi : MonotoneOn phi s)
    {C : ℝ≥0} (hf : LipschitzOnWith C (f ∘ phi) s) {a : ℝ} (ha : a ∈ s) :
    LipschitzOnWith C (fun x => variationOnFromTo f (phi '' s) (phi a) (phi x)) s := by
  have hLip := lipschitzOnWith_variationOnFromTo hf ha
  intro x hx y hy
  change edist (variationOnFromTo f (phi '' s) (phi a) (phi x))
    (variationOnFromTo f (phi '' s) (phi a) (phi y)) ≤ _
  rw [← variationOnFromTo.comp_eq_of_monotoneOn f phi hphi ha hx,
    ← variationOnFromTo.comp_eq_of_monotoneOn f phi hphi ha hy]
  exact hLip hx hy

end PoincareConjecture.M60
