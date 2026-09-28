import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Smooth.Coercivity









noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.NirenbergTestFunction
open Poincare.Analysis.Sobolev.NirenbergSubstitution
open Poincare.Analysis.Sobolev.NirenbergCoercivity
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Poincare.Analysis.Sobolev.NirenbergCrossBounds

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem lintegral_sq_diffQuot_le_local
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    {K : Set E} (_hK : MeasurableSet K) :
    ∫⁻ x in K, (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure E) ≤
      ∫⁻ y in Metric.cthickening |h| K,
        (‖(fderiv ℝ v y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2
        ∂(volume : Measure E) := by
  set e : E := EuclideanSpace.single k (1 : ℝ) with he
  set H : E → ℝ≥0∞ := fun y => (‖(fderiv ℝ v y) e‖ₑ : ℝ≥0∞) ^ 2 with hH_def
  have hfd_cont : Continuous (fun y : E => fderiv ℝ v y) :=
    hv.continuous_fderiv one_ne_zero
  have h_partial_cont : Continuous (fun y : E => (fderiv ℝ v y) e) :=
    hfd_cont.clm_apply continuous_const
  have hH_meas : Measurable H := by
    rw [hH_def]
    exact h_partial_cont.measurable.enorm.pow_const 2
  have hPair_meas :
      Measurable (fun p : E × ℝ => H (p.1 + (p.2 * h) • e)) := by
    have h1 : Measurable (fun p : E × ℝ => p.1) := measurable_fst
    have h2 : Measurable (fun p : E × ℝ => p.2) := measurable_snd
    have h3 : Measurable (fun p : E × ℝ => p.2 * h) :=
      h2.mul measurable_const
    have h4 : Measurable (fun p : E × ℝ => (p.2 * h) • e) :=
      h3.smul measurable_const
    have h5 : Measurable (fun p : E × ℝ => p.1 + (p.2 * h) • e) :=
      h1.add h4
    exact hH_meas.comp h5
  have hpt : ∀ x : E,
      (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 ≤
        ∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e) := by
    intro x
    have hreal := sq_diffQuot_le_integral_sq_partialDeriv (d := d) hv k hh x
    have hLHS_eq :
        (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 =
          ENNReal.ofReal ((diffQuot k h v x) ^ 2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have hgamma_cont : Continuous (fun s : ℝ => x + (s * h) • e) :=
      continuous_const.add
        ((continuous_id.mul continuous_const).smul continuous_const)
    have hreal_int_cont : Continuous (fun s : ℝ =>
        ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) :=
      ((h_partial_cont.comp hgamma_cont)).pow 2
    have hreal_int :
        Integrable (fun s : ℝ => ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2)
          ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
      hreal_int_cont.integrableOn_Ioc (a := 0) (b := 1)
    have hConvert :
        ENNReal.ofReal
            (∫ s in Set.Ioc (0 : ℝ) 1,
              ((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) =
          ∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e) := by
      rw [ofReal_integral_eq_lintegral_ofReal hreal_int
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
      refine lintegral_congr_ae ?_
      filter_upwards with s
      change ENNReal.ofReal (((fderiv ℝ v (x + (s * h) • e)) e) ^ 2) =
        (‖(fderiv ℝ v (x + (s * h) • e)) e‖ₑ : ℝ≥0∞) ^ 2
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [hLHS_eq, ← hConvert]
    exact ENNReal.ofReal_le_ofReal hreal
  have h_step12 :
      ∫⁻ x in K, (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure E) ≤
        ∫⁻ x in K,
          (∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e))
          ∂(volume : Measure E) := by
    refine lintegral_mono ?_
    intro x; exact hpt x
  have h_swap :
      ∫⁻ x in K,
          ∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e) ∂(volume : Measure ℝ)
          ∂(volume : Measure E) =
        ∫⁻ s in Set.Ioc (0 : ℝ) 1,
          ∫⁻ x in K, H (x + (s * h) • e) ∂(volume : Measure E)
          ∂(volume : Measure ℝ) := by
    exact lintegral_lintegral_swap hPair_meas.aemeasurable
  have hTrans : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 →
      ∫⁻ x in K, H (x + (s * h) • e) ∂(volume : Measure E) ≤
        ∫⁻ y in Metric.cthickening |h| K, H y ∂(volume : Measure E) := by
    intro s hs
    have hMP : MeasurePreserving
        (fun x : E => x + (s * h) • e) volume volume :=
      measurePreserving_add_right volume _
    have hME : MeasurableEmbedding (fun x : E => x + (s * h) • e) :=
      (Homeomorph.addRight ((s * h) • e)).measurableEmbedding
    have h_change :
        ∫⁻ x in K, H (x + (s * h) • e) ∂(volume : Measure E) =
          ∫⁻ y in (fun x : E => x + (s * h) • e) '' K, H y
            ∂(volume : Measure E) :=
      hMP.setLIntegral_comp_emb hME H K
    rw [h_change]
    have h_subset : (fun x : E => x + (s * h) • e) '' K ⊆
        Metric.cthickening |h| K := by
      intro y hy
      obtain ⟨x, hxK, hxy⟩ := hy
      refine Metric.mem_cthickening_of_dist_le _ x |h| K hxK ?_
      have hdist_eq : dist y x = ‖(s * h) • e‖ := by
        rw [dist_eq_norm, ← hxy]
        change ‖(x + (s * h) • e) - x‖ = ‖(s * h) • e‖
        rw [add_sub_cancel_left]
      rw [hdist_eq]
      have hsing_norm :
          ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
      rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
      have hs_nn : 0 ≤ s := le_of_lt hs.1
      have hs_le_one : s ≤ 1 := hs.2
      have habs_eq : |s * h| = s * |h| := by
        rw [abs_mul, abs_of_nonneg hs_nn]
      rw [habs_eq]
      have habs_h_nn : 0 ≤ |h| := abs_nonneg h
      calc s * |h| ≤ 1 * |h| :=
              mul_le_mul_of_nonneg_right hs_le_one habs_h_nn
        _ = |h| := one_mul _
    exact lintegral_mono_set h_subset
  calc ∫⁻ x in K, (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume : Measure E)
      ≤ ∫⁻ x in K,
            (∫⁻ s in Set.Ioc (0 : ℝ) 1, H (x + (s * h) • e))
            ∂(volume : Measure E) := h_step12
    _ = ∫⁻ s in Set.Ioc (0 : ℝ) 1,
            ∫⁻ x in K, H (x + (s * h) • e) ∂(volume : Measure E)
          ∂((volume : Measure ℝ)) := h_swap
    _ ≤ ∫⁻ _s in Set.Ioc (0 : ℝ) 1,
            ∫⁻ y in Metric.cthickening |h| K, H y ∂(volume : Measure E)
          ∂((volume : Measure ℝ)) := by
        refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
        refine Filter.Eventually.of_forall ?_
        intro s hs
        exact hTrans s hs
    _ = ∫⁻ y in Metric.cthickening |h| K, H y ∂(volume : Measure E) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ]
        simp [Real.volume_Ioc]

omit [NeZero d] in
theorem integral_sq_diffQuot_le_local
    {v : E → ℝ} (hv : ContDiff ℝ 1 v) (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    {K : Set E} (hK : MeasurableSet K)
    (h_thick_int : Integrable
      (fun y : E => ((fderiv ℝ v y) (EuclideanSpace.single k 1)) ^ 2)
      ((volume : Measure E).restrict (Metric.cthickening |h| K))) :
    ∫ x in K, (diffQuot k h v x) ^ 2 ∂(volume : Measure E) ≤
      ∫ y in Metric.cthickening |h| K,
        ((fderiv ℝ v y) (EuclideanSpace.single k 1)) ^ 2
        ∂(volume : Measure E) := by
  set fL : E → ℝ := fun x => (diffQuot k h v x) ^ 2 with hfL_def
  set fR : E → ℝ := fun y => ((fderiv ℝ v y) (EuclideanSpace.single k 1)) ^ 2
    with hfR_def
  have hLHS_nonneg : ∀ x : E, 0 ≤ fL x := fun _ => sq_nonneg _
  have hRHS_nonneg : ∀ y : E, 0 ≤ fR y := fun _ => sq_nonneg _
  have h_lintegral := lintegral_sq_diffQuot_le_local (d := d) hv k hh hK
  have h_norm_LHS : ∀ x : E,
      (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (fL x) := by
    intro x
    change (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((diffQuot k h v x) ^ 2)
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  have h_norm_RHS : ∀ y : E,
      (‖(fderiv ℝ v y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2 =
        ENNReal.ofReal (fR y) := by
    intro y
    change (‖(fderiv ℝ v y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2 =
      ENNReal.ofReal (((fderiv ℝ v y) (EuclideanSpace.single k 1)) ^ 2)
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]
  have h_lintegral_real :
      ∫⁻ x in K, ENNReal.ofReal (fL x) ∂(volume : Measure E) ≤
        ∫⁻ y in Metric.cthickening |h| K, ENNReal.ofReal (fR y)
          ∂(volume : Measure E) := by
    have h1 : (fun x : E => (‖diffQuot k h v x‖ₑ : ℝ≥0∞) ^ 2) =
        fun x : E => ENNReal.ofReal (fL x) := by
      funext x; exact h_norm_LHS x
    have h2 : (fun y : E => (‖(fderiv ℝ v y) (EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞) ^ 2) =
        fun y : E => ENNReal.ofReal (fR y) := by
      funext y; exact h_norm_RHS y
    rw [← h1, ← h2]; exact h_lintegral
  have hRHS_fin : ∫⁻ y in Metric.cthickening |h| K, ENNReal.ofReal (fR y)
        ∂(volume : Measure E) ≠ ∞ := by
    have h := h_thick_int
    rw [← ofReal_integral_eq_lintegral_ofReal h
      (Filter.Eventually.of_forall hRHS_nonneg)]
    exact ENNReal.ofReal_ne_top
  have hLHS_fin : ∫⁻ x in K, ENNReal.ofReal (fL x) ∂(volume : Measure E) ≠ ∞ :=
    fun h_eq_top => hRHS_fin (le_antisymm le_top
      (by rw [← h_eq_top]; exact h_lintegral_real))
  have hL_meas : AEStronglyMeasurable fL ((volume : Measure E).restrict K) := by
    have hfL_cont : Continuous fL := by
      have hfL_cont : Continuous (diffQuot k h v) := by
        by_cases hh0 : h = 0
        · subst hh0
          rw [diffQuot_zero_h]
          exact continuous_const
        · have hv_cont : Continuous v := hv.continuous
          have h_translate :
              Continuous (fun x : E => v (x + h • EuclideanSpace.single k 1)) := by
            have h_add : Continuous (fun x : E => x + h • EuclideanSpace.single k 1) :=
              continuous_id.add continuous_const
            exact hv_cont.comp h_add
          have h_diff : Continuous (fun x : E =>
              v (x + h • EuclideanSpace.single k 1) - v x) :=
            h_translate.sub hv_cont
          have h_div : Continuous (fun x : E =>
              (v (x + h • EuclideanSpace.single k 1) - v x) / h) :=
            h_diff.div_const h
          have heq : (diffQuot k h v) =
              fun x : E => (v (x + h • EuclideanSpace.single k 1) - v x) / h := by
            funext x
            exact diffQuot_apply_of_ne (d := d) k hh0 v x
          rw [heq]; exact h_div
      exact hfL_cont.pow 2
    exact hfL_cont.aestronglyMeasurable
  have hL_int : Integrable fL ((volume : Measure E).restrict K) := by
    refine ⟨hL_meas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have h_eq : ∀ x : E, (‖fL x‖ₑ : ℝ≥0∞) = ENNReal.ofReal (fL x) := by
      intro x
      rw [Real.enorm_eq_ofReal (hLHS_nonneg x)]
    have heq_lin : ∫⁻ x in K, (‖fL x‖ₑ : ℝ≥0∞) ∂(volume : Measure E) =
        ∫⁻ x in K, ENNReal.ofReal (fL x) ∂(volume : Measure E) :=
      lintegral_congr (fun x => h_eq x)
    rw [heq_lin]
    exact lt_of_le_of_lt (le_refl _) (lt_of_le_of_ne le_top hLHS_fin)
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hLHS_nonneg) hL_meas]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hRHS_nonneg) h_thick_int.aestronglyMeasurable]
  exact ENNReal.toReal_mono hRHS_fin h_lintegral_real

omit [NeZero d] in
private theorem integral_diffQuot_sq_on_tsupport_le
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (η : E → ℝ)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_compact : IsCompact (closure Ω'))
    (hh_supp_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω') :
    ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
      ∫ x in Ω', ((fderiv ℝ u x) (EuclideanSpace.single k 1))^2
        ∂(volume : Measure E) := by
  have h_tsupp_meas : MeasurableSet (tsupport η) :=
    isClosed_tsupport η |>.measurableSet
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  have h_deriv_cont : Continuous (fun y : E =>
      ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2) := by
    have h_fderiv_cont : Continuous (fderiv ℝ u) :=
      hu_C1.continuous_fderiv (by norm_num)
    exact (h_fderiv_cont.clm_apply continuous_const).pow 2
  have h_thick_compact : IsCompact (Metric.cthickening |h| (tsupport η)) := by
    have h_thick_closed : IsClosed (Metric.cthickening |h| (tsupport η)) :=
      isClosed_cthickening
    have h_thick_subset_clO : Metric.cthickening |h| (tsupport η) ⊆ closure Ω' :=
      hh_supp_in_Ω'.trans subset_closure
    exact hΩ'_compact.of_isClosed_subset h_thick_closed h_thick_subset_clO
  have h_thick_int :
      Integrable (fun y : E =>
          ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2)
        ((volume : Measure E).restrict (Metric.cthickening |h| (tsupport η))) := by
    refine ContinuousOn.integrableOn_compact h_thick_compact ?_
    exact h_deriv_cont.continuousOn
  have h_local := integral_sq_diffQuot_le_local (d := d) hu_C1 k hh
    h_tsupp_meas h_thick_int
  have h_Ω'_meas : MeasurableSet Ω' := hΩ'.measurableSet
  have h_clΩ'_int :
      Integrable (fun y : E =>
          ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2)
        ((volume : Measure E).restrict (closure Ω')) :=
    ContinuousOn.integrableOn_compact hΩ'_compact h_deriv_cont.continuousOn
  have h_Ω'_int :
      Integrable (fun y : E =>
          ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2)
        ((volume : Measure E).restrict Ω') := by
    have : (volume : Measure E).restrict Ω' ≤ (volume : Measure E).restrict (closure Ω') :=
      Measure.restrict_mono subset_closure (le_refl _)
    exact h_clΩ'_int.mono_measure this
  have h_setIntegral_mono :
      ∫ y in Metric.cthickening |h| (tsupport η),
          ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2
          ∂(volume : Measure E) ≤
        ∫ y in Ω', ((fderiv ℝ u y) (EuclideanSpace.single k 1))^2
          ∂(volume : Measure E) := by
    refine setIntegral_mono_set h_Ω'_int ?_ ?_
    · refine Filter.Eventually.of_forall ?_; intro x; exact sq_nonneg _
    · exact (Filter.Eventually.of_forall hh_supp_in_Ω').mono (fun _ h => h)
  exact h_local.trans h_setIntegral_mono

noncomputable def absorbingIntegral
    (k : Fin d) (h : ℝ) (η u : E → ℝ) : ℝ :=
  ∫ x, (η x)^2 *
      ∑ i : Fin d, Poincare.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
    ∂(volume : Measure E)

noncomputable def gradL2sqOn (Ω' : Set E) (u : E → ℝ) : ℝ :=
  ∫ x in Ω',
      ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
    ∂(volume : Measure E)

omit [NeZero d] in
lemma absorbingIntegral_nonneg
    (k : Fin d) (h : ℝ) (η u : E → ℝ) :
    0 ≤ absorbingIntegral (d := d) k h η u := by
  unfold absorbingIntegral
  refine integral_nonneg ?_
  intro x
  refine mul_nonneg (sq_nonneg _) ?_
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [NeZero d] in
private lemma gradL2sqOn_nonneg (Ω' : Set E) (u : E → ℝ) :
    0 ≤ gradL2sqOn (d := d) Ω' u := by
  unfold gradL2sqOn
  refine integral_nonneg ?_
  intro x
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [NeZero d] in
theorem integral_diffQuot_sq_on_tsupport_le_gradL2sqOn
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (η : E → ℝ)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_compact : IsCompact (closure Ω'))
    (hh_supp_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω') :
    ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
      gradL2sqOn (d := d) Ω' u := by
  have h_step1 := integral_diffQuot_sq_on_tsupport_le (d := d) hu k hh η hΩ'
    hΩ'_compact hh_supp_in_Ω'
  refine h_step1.trans ?_
  unfold gradL2sqOn
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  have h_fderiv_cont : Continuous (fderiv ℝ u) :=
    hu_C1.continuous_fderiv (by norm_num)
  have h_partial_cont : ∀ i : Fin d,
      Continuous (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
    fun i => h_fderiv_cont.clm_apply continuous_const
  have h_partial_sq_cont : ∀ i : Fin d,
      Continuous (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
    fun i => (h_partial_cont i).pow 2
  have h_clΩ'_int : ∀ i : Fin d, Integrable
      (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)
      ((volume : Measure E).restrict (closure Ω')) :=
    fun i => ContinuousOn.integrableOn_compact hΩ'_compact (h_partial_sq_cont i).continuousOn
  have h_Ω'_int : ∀ i : Fin d, Integrable
      (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)
      ((volume : Measure E).restrict Ω') :=
    fun i => (h_clΩ'_int i).mono_measure (Measure.restrict_mono subset_closure (le_refl _))
  have h_sum_int : Integrable (fun x : E =>
      ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)
      ((volume : Measure E).restrict Ω') :=
    integrable_finsetSum _ (fun i _ => h_Ω'_int i)
  refine setIntegral_mono_on (h_Ω'_int k) h_sum_int hΩ'.measurableSet ?_
  intro x _
  refine Finset.single_le_sum (f := fun i =>
      ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ?_ (Finset.mem_univ k)
  intro i _
  exact sq_nonneg _

end Poincare.Analysis.Sobolev.NirenbergCrossBounds
