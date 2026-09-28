import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

universe u

lemma Poincare.Parabolic.hasDerivAt_integral_compact_support
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    [IsFiniteMeasureOnCompacts μ]
    {U : Set ℝ} (hU : IsOpen U) {F G : ℝ → X → ℝ}
    (hF : ContinuousOn F.uncurry (U ×ˢ univ))
    (hG : ContinuousOn G.uncurry (U ×ˢ univ))
    {K : Set X} (hK : IsCompact K)
    (hFK : ∀ t ∈ U, ∀ x ∉ K, F t x = 0)
    (hGK : ∀ t ∈ U, ∀ x ∉ K, G t x = 0)
    (hd : ∀ t ∈ U, ∀ x, HasDerivAt (fun s ↦ F s x) (G t x) t)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun s ↦ ∫ x, F s x ∂μ) (∫ x, G t x ∂μ) t := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU t ht
  have hcl : Metric.closedBall t (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hFc (s : ℝ) (hs : s ∈ U) : Continuous (F s) := by
    rw [← continuousOn_univ]
    exact hF.comp (continuousOn_const.prodMk continuousOn_id) (fun x _ ↦ ⟨hs, mem_univ x⟩)
  have hGc (s : ℝ) (hs : s ∈ U) : Continuous (G s) := by
    rw [← continuousOn_univ]
    exact hG.comp (continuousOn_const.prodMk continuousOn_id) (fun x _ ↦ ⟨hs, mem_univ x⟩)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t (r / 2)).prod hK).exists_bound_of_continuousOn
    (hG.mono (prod_mono hcl (subset_univ K)))
  have hb : Integrable (K.indicator (fun _ : X ↦ C)) μ :=
    (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.closedBall_mem_nhds t (by positivity : 0 < r / 2))
    ?_ ?_ (hGc t ht).aestronglyMeasurable ?_ hb ?_).2
  · filter_upwards [hU.mem_nhds ht] with s hs
    exact (hFc s hs).aestronglyMeasurable
  · exact (hFc t ht).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hK
        (by intro x hx; by_contra h; exact hx (hFK t ht x h)))
  · filter_upwards [] with x
    intro s hs
    by_cases hx : x ∈ K
    · simpa only [indicator_of_mem hx, Function.uncurry] using hC (s, x) ⟨hs, hx⟩
    · simp [indicator_of_notMem hx, hGK s (hcl hs) x hx]
  · exact ae_of_all _ (fun x s hs ↦ hd s (hcl hs) x)

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}

private lemma positive_time_germ {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    {t : ℝ} (ht : 0 < t) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, x) :=
  hF.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)



theorem hasDerivAt_cutoff_square_integral
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ ∫ x, η x ^ 2 * F (s, x) ^ 2 ∂g.volumeMeasure)
      (∫ x, η x ^ 2 * deriv (fun s ↦ F (s, x) ^ 2) t ∂g.volumeMeasure) t := by
  have hdcont : ContinuousOn
      (fun p : ℝ × M ↦ η p.2 ^ 2 * deriv (fun s ↦ F (s, p.2) ^ 2) p.1)
      (Ioi 0 ×ˢ univ) := by
    intro p hp
    have h := (((hη p.2).comp p contMDiffAt_snd).pow 2).mul
      (Poincare.Manifold.contMDiffAt_deriv_time ((positive_time_germ hF hp.1 p.2).pow 2))
    exact h.continuousAt.continuousWithinAt
  refine Poincare.Parabolic.hasDerivAt_integral_compact_support (μ := g.volumeMeasure)
    (F := fun s x ↦ η x ^ 2 * F (s, x) ^ 2)
    (G := fun s x ↦ η x ^ 2 * deriv (fun r ↦ F (r, x) ^ 2) s) isOpen_Ioi
    (by
      convert (((hη.continuous.comp continuous_snd).pow 2).continuousOn.mul
        (hF.continuousOn.pow 2)) using 1
      funext p
      rfl)
    hdcont hηc.isCompact ?_ ?_ ?_ ht
  · intro s _ x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  · intro s _ x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  · intro s hs x
    have h := ((positive_time_germ hF hs x).comp s
      (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt.differentiableAt (by simp)
    simpa only [Function.comp_def, id_eq, Pi.pow_def] using
      (h.pow 2).hasDerivAt.const_mul (η x ^ 2)




theorem integrated_heat_energy_cutoff_estimate (D : LeviCivitaData g)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    let Q := fun t ↦ ∫ x, η x ^ 2 * g.inner x
      (D.gradient (fun y ↦ F (t, y)) x) (D.gradient (fun y ↦ F (t, y)) x)
      ∂g.volumeMeasure
    IntervalIntegrable Q volume a b ∧
      (∫ t in a..b, Q t) ≤ (∫ x, η x ^ 2 * F (a, x) ^ 2 ∂g.volumeMeasure) +
        4 * ∫ t in a..b, ∫ x, F (t, x) ^ 2 *
          g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure := by
  dsimp only
  let E := fun t ↦ ∫ x, η x ^ 2 * F (t, x) ^ 2 ∂g.volumeMeasure
  let E' := fun t ↦ ∫ x, η x ^ 2 * deriv (fun s ↦ F (s, x) ^ 2) t ∂g.volumeMeasure
  let W := fun t ↦ ∫ x, F (t, x) ^ 2 *
    g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure
  let Q := fun t ↦ ∫ x, η x ^ 2 * g.inner x
    (D.gradient (fun y ↦ F (t, y)) x) (D.gradient (fun y ↦ F (t, y)) x)
    ∂g.volumeMeasure
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun _ ht ↦ ha.trans_le ht.1
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt E (E' t) t :=
    hasDerivAt_cutoff_square_integral hF hη hηc ht
  have hEc : ContinuousOn E (Icc a b) :=
    fun t ht ↦ (hd t (hsub ht)).continuousAt.continuousWithinAt
  have hE'c : ContinuousOn E' (Ioi 0) := by
    apply continuousOn_integral_of_compact_support hηc.isCompact
    · intro p hp
      have h := (((hη p.2).comp p contMDiffAt_snd).pow 2).mul
        (Poincare.Manifold.contMDiffAt_deriv_time ((positive_time_germ hF hp.1 p.2).pow 2))
      exact h.continuousAt.continuousWithinAt
    · intro t x _ hx
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hWc : ContinuousOn W (Ioi 0) := by
    apply continuousOn_integral_of_compact_support hηc.isCompact
    · exact (hF.continuousOn.pow 2).mul
        ((D.continuous_inner_gradient hη hη).comp continuous_snd).continuousOn
    · intro t x _ hx
      simp [D.gradient_eq_zero_of_notMem_tsupport hx]
  have hQi (t : ℝ) (ht : 0 < t) : Q t ≤ 4 * W t - E' t := by
    have h := D.heat_energy_cutoff_estimate (positive_time_germ hF ht)
      (hheat t ht) hη hηc
    change E' t + Q t ≤ 4 * W t at h
    linarith
  have hQ0 (t : ℝ) : 0 ≤ Q t := by
    apply integral_nonneg
    intro x
    apply mul_nonneg (sq_nonneg _)
    by_cases hv : D.gradient (fun y ↦ F (t, y)) x = 0
    · simp [hv]
    · exact (g.pos x _ hv).le


  have hQm : StronglyMeasurable (fun t ↦ Q (max a t)) := by
    apply StronglyMeasurable.integral_prod_right
    apply Measurable.stronglyMeasurable
    apply measurable_uncurry_of_continuous_of_measurable
    · intro x
      apply continuous_const.mul
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (D.hasDerivAt_gradient_normSq_of_time_derivative
        (positive_time_germ hF (ha.trans_le (le_max_left _ _)) x)
        (hheat (max a t) (ha.trans_le (le_max_left _ _)))).continuousAt.comp
          ((continuous_const.max continuous_id).continuousAt)
    · intro t
      have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y ↦ F (max a t, y)) :=
        fun x ↦ (positive_time_germ hF (ha.trans_le (le_max_left _ _)) x).comp x
          (contMDiffAt_const.prodMk contMDiffAt_id)
      exact ((hη.continuous.pow 2).mul (D.continuous_inner_gradient hs hs)).measurable
  have hWint : IntervalIntegrable W volume a b :=
    (hWc.mono hsub).intervalIntegrable_of_Icc hab
  have hE'int : IntervalIntegrable E' volume a b :=
    (hE'c.mono hsub).intervalIntegrable_of_Icc hab
  have hQint : IntervalIntegrable Q volume a b := by
    apply ((hWint.const_mul 4).sub hE'int).mono_fun' ?_ ?_
    · apply hQm.aestronglyMeasurable.congr
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [uIoc_of_le hab] at ht
      simp only [max_eq_right ht.1.le]
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [uIoc_of_le hab] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 t)]
      exact hQi t (ha.trans ht.1)
  have hi := intervalIntegral.integral_mono_on hab hQint ((hWint.const_mul 4).sub hE'int)
    (fun t ht ↦ hQi t (hsub ht))
  rw [intervalIntegral.integral_sub (hWint.const_mul 4) hE'int,
    intervalIntegral.integral_const_mul] at hi
  have hFTC : (∫ t in a..b, E' t) = E b - E a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦ hd t (hsub (by simpa only [uIcc_of_le hab] using ht))) hE'int
  rw [hFTC] at hi
  have hEb : 0 ≤ E b := integral_nonneg (fun x ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact ⟨hQint, by change (∫ t in a..b, Q t) ≤ E a + 4 * ∫ t in a..b, W t; linarith⟩




theorem integrated_heat_energy_cutoff_estimate_from_zero (D : LeviCivitaData g)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hFc : ContinuousOn F (Ici 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) {b : ℝ} (hb : 0 < b) :
    let Q := fun t ↦ ∫ x, η x ^ 2 * g.inner x
      (D.gradient (fun y ↦ F (t, y)) x) (D.gradient (fun y ↦ F (t, y)) x)
      ∂g.volumeMeasure
    IntervalIntegrable Q volume 0 b ∧
      (∫ t in 0..b, Q t) ≤ (∫ x, η x ^ 2 * F (0, x) ^ 2 ∂g.volumeMeasure) +
        4 * ∫ t in 0..b, ∫ x, F (t, x) ^ 2 *
          g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure := by
  dsimp only
  let E := fun t ↦ ∫ x, η x ^ 2 * F (t, x) ^ 2 ∂g.volumeMeasure
  let W := fun t ↦ ∫ x, F (t, x) ^ 2 *
    g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure
  let Q := fun t ↦ ∫ x, η x ^ 2 * g.inner x
    (D.gradient (fun y ↦ F (t, y)) x) (D.gradient (fun y ↦ F (t, y)) x)
    ∂g.volumeMeasure
  have hsub : Icc (0 : ℝ) b ⊆ Ici 0 := fun _ ht ↦ ht.1
  have hEc : ContinuousOn E (Icc 0 b) := by
    apply (continuousOn_integral_of_compact_support hηc.isCompact ?_ ?_).mono hsub
    · convert (((hη.continuous.comp continuous_snd).pow 2).continuousOn.mul
        (hFc.pow 2)) using 1
      funext p
      rfl
    · intro t x _ hx
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hWc : ContinuousOn W (Icc 0 b) := by
    apply (continuousOn_integral_of_compact_support hηc.isCompact ?_ ?_).mono hsub
    · exact (hFc.pow 2).mul
        ((D.continuous_inner_gradient hη hη).comp continuous_snd).continuousOn
    · intro t x _ hx
      simp [D.gradient_eq_zero_of_notMem_tsupport hx]
  have hinner0 (x : M) (v : TangentSpace (𝓡 n) x) : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hQ0 (t : ℝ) : 0 ≤ Q t :=
    integral_nonneg (fun x ↦ mul_nonneg (sq_nonneg _) (hinner0 x _))
  have hW0 (t : ℝ) : 0 ≤ W t :=
    integral_nonneg (fun x ↦ mul_nonneg (sq_nonneg _) (hinner0 x _))
  have hWi : IntervalIntegrable W volume 0 b := hWc.intervalIntegrable_of_Icc hb.le
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hEc
  let a : ℕ → ℝ := fun j ↦ b / ((j : ℝ) + 1)
  have ha (j : ℕ) : 0 < a j := by dsimp [a]; positivity
  have hab (j : ℕ) : a j ≤ b := by
    dsimp [a]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  have halim : Tendsto a atTop (𝓝 0) := by
    simpa [a] using tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hi (j : ℕ) : IntervalIntegrable Q volume (a j) b ∧
      (∫ t in a j..b, Q t) ≤ E (a j) + 4 * ∫ t in a j..b, W t :=
    D.integrated_heat_energy_cutoff_estimate hF hheat hη hηc (ha j) (hab j)
  have hQi : IntervalIntegrable Q volume 0 b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
    apply integrableOn_Ioc_of_intervalIntegral_norm_bounded_left
      (fun j ↦ (hi j).1.1) halim
    apply Eventually.of_forall
    intro j
    have hnorm : (∫ t in Ioc (a j) b, ‖Q t‖) = ∫ t in a j..b, Q t := by
      rw [intervalIntegral.integral_of_le (hab j)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t _
      exact Real.norm_of_nonneg (hQ0 t)
    rw [hnorm]
    have hWB := intervalIntegral.integral_mono_interval (ha j).le (hab j) le_rfl
      (ae_of_all _ hW0) hWi
    have hEB : E (a j) ≤ B := (le_abs_self _).trans (hB (a j) ⟨(ha j).le, hab j⟩)
    exact (hi j).2.trans (add_le_add hEB (mul_le_mul_of_nonneg_left hWB (by norm_num)))
  have haI (j : ℕ) : a j ∈ uIcc (0 : ℝ) b := by
    simpa only [uIcc_of_le hb.le, mem_Icc] using And.intro (ha j).le (hab j)
  have hlimQ : Tendsto (fun j ↦ ∫ t in a j..b, Q t) atTop (𝓝 (∫ t in 0..b, Q t)) := by
    have hc := (intervalIntegral.continuousOn_primitive_interval' hQi right_mem_uIcc).neg
    simpa only [Function.comp_def, Pi.neg_apply, ← intervalIntegral.integral_symm] using
      (hc 0 left_mem_uIcc).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨halim, Eventually.of_forall haI⟩)
  have hlimW : Tendsto (fun j ↦ ∫ t in a j..b, W t) atTop (𝓝 (∫ t in 0..b, W t)) := by
    have hc := (intervalIntegral.continuousOn_primitive_interval' hWi right_mem_uIcc).neg
    simpa only [Function.comp_def, Pi.neg_apply, ← intervalIntegral.integral_symm] using
      (hc 0 left_mem_uIcc).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨halim, Eventually.of_forall haI⟩)
  have hlimE : Tendsto (fun j ↦ E (a j)) atTop (𝓝 (E 0)) :=
    (hEc 0 ⟨le_rfl, hb.le⟩).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨halim, Eventually.of_forall (fun j ↦ ⟨(ha j).le, hab j⟩)⟩)
  exact ⟨hQi, le_of_tendsto_of_tendsto' hlimQ (hlimE.add (hlimW.const_mul 4))
    (fun j ↦ (hi j).2)⟩

end PoincareConjecture.LeviCivitaData
