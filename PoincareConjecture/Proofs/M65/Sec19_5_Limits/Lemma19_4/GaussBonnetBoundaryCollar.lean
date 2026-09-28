import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetCommonCollar
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryTangent
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetRadialConnection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory Complex InnerProductSpace
open scoped Topology ContDiff

namespace PoincareConjecture.M65Gauss

open M65Branch

def weightedMetricDual {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (H N : ℂ → EuclideanSpace ℝ (Fin n)) (w : ℂ → ℝ) (z : ℂ) :
    EuclideanSpace ℝ (Fin n) :=
  w z • (toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (g.euclideanCoefficients (H z) (N z))

theorem inner_weightedMetricDual {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (H N : ℂ → EuclideanSpace ℝ (Fin n)) (w : ℂ → ℝ)
    (z : ℂ) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ v (weightedMetricDual g H N w z) = w z * g.inner (H z) v (N z) := by
  rw [weightedMetricDual, inner_smul_right, real_inner_comm, toDual_symm_apply]
  rw [g.symm]
  rfl

theorem weightedMetricDual_regularity {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    {H N : ℂ → EuclideanSpace ℝ (Fin n)} {w : ℂ → ℝ}
    {K U : Set ℂ} (hK : IsCompact K) (hKU : UniqueDiffOn ℝ K)
    (hU : IsOpen U) (hUK : U ⊆ K)
    (hH : ContDiffOn ℝ 1 H K) (hw : ContDiffOn ℝ 1 w K)
    (hN : ContinuousOn N K) (hN1 : ContDiffOn ℝ 1 N U) (v : ℂ)
    (hDN : MemLp (fun z => fderiv ℝ N z v) 2 (volume.restrict (K ∩ U))) :
    ContinuousOn (weightedMetricDual g H N w) K ∧
      ContDiffOn ℝ 1 (weightedMetricDual g H N w) U ∧
      MemLp (fun z => fderiv ℝ (weightedMetricDual g H N w) z v)
        2 (volume.restrict (K ∩ U)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let R := (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let q : ℂ → E × (E × ℝ) := fun z => (H z, N z, w z)
  let A : E × (E × ℝ) → E := fun p => p.2.2 • R (g.euclideanCoefficients p.1 p.2.1)
  have hG : ContDiff ℝ 1 g.euclideanCoefficients :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).of_le (by simp)
  have hA : ContDiff ℝ 1 A :=
    (contDiff_snd.snd).smul
      (R.contDiff.comp ((hG.comp contDiff_fst).clm_apply contDiff_snd.fst))
  have hq : ContinuousOn q K := hH.continuousOn.prodMk (hN.prodMk hw.continuousOn)
  have hq1 : ContDiffOn ℝ 1 q U := (hH.mono hUK).prodMk (hN1.prodMk (hw.mono hUK))
  have hDH := compact_within_derivative_memLp hK hKU hU hUK hH v
  have hDw := compact_within_derivative_memLp hK hKU hU hUK hw v
  have hraw : MemLp (fun z => (fderiv ℝ H z v, fderiv ℝ N z v, fderiv ℝ w z v))
      2 (volume.restrict (K ∩ U)) :=
    memLp_prod_iff.mpr ⟨hDH, memLp_prod_iff.mpr ⟨hDN, hDw⟩⟩
  have hDq : MemLp (fun z => fderiv ℝ q z v) 2 (volume.restrict (K ∩ U)) := by
    apply hraw.ae_eq
    filter_upwards [ae_restrict_mem (hK.measurableSet.inter hU.measurableSet)] with z hz
    have hHz := ((hH.mono hUK).contDiffAt (hU.mem_nhds hz.2)).differentiableAt one_ne_zero
    have hNz := (hN1.contDiffAt (hU.mem_nhds hz.2)).differentiableAt one_ne_zero
    have hwz := ((hw.mono hUK).contDiffAt (hU.mem_nhds hz.2)).differentiableAt one_ne_zero
    exact (congrArg (fun L : ℂ →L[ℝ] E × (E × ℝ) => L v)
      (hHz.hasFDerivAt.prodMk (hNz.hasFDerivAt.prodMk hwz.hasFDerivAt)).fderiv).symm
  have hcomp := actual_comp_derivative_memLp hK hU isOpen_univ hq hq1
    (mapsTo_univ _ _) hA.contDiffOn v hDq
  exact ⟨hA.continuous.comp_continuousOn hq, hA.comp_contDiffOn hq1, hcomp⟩

private theorem interval_flux_tendsto_of_pointwise
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T N : ℕ → ℝ → E} {U V : ℝ → E} {delta : ℕ → ℝ} {a b C L : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hd : ∀ n, 0 ≤ delta n) (hdt : Tendsto delta atTop (𝓝 0))
    (hT : ∀ n, ∀ t ∈ Icc a b, ContDiffAt ℝ 1 (T n) t)
    (hN : ∀ n, ∀ t ∈ Icc a b, ContDiffAt ℝ 1 (N n) t)
    (hU : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 U t)
    (hclose : ∀ n, ∀ t ∈ Icc a b, ‖T n t - U t‖ ≤ C * Real.sqrt (delta n))
    (hbound : ∀ n, ∀ t ∈ Icc a b, ‖N n t‖ ≤ L)
    (hNlim : ∀ t ∈ Icc a b, Tendsto (fun n => N n t) atTop (𝓝 (V t)))
    (henergy : Tendsto (fun n => delta n * ∫ t in a..b, ‖deriv (N n) t‖ ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t in a..b, inner ℝ (deriv (T n) t) (N n t)) atTop
      (𝓝 (∫ t in a..b, inner ℝ (deriv U t) (V t))) := by
  let err := fun n => (∫ t in a..b, inner ℝ (deriv (T n) t) (N n t)) -
    ∫ t in a..b, inner ℝ (deriv U t) (N n t)
  have herrsq : Tendsto (fun n => err n ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg (err n))
      (fun n => collar_interval_flux_sq_bound hab hC hL (hd n) (hT n) hU (hN n)
        (hclose n) (hbound n))
    have hh := (hdt.const_mul (8 * C ^ 2 * L ^ 2)).add
      (henergy.const_mul (2 * C ^ 2 * (b - a)))
    have heq : (fun n =>
        2 * C ^ 2 * delta n * (4 * L ^ 2 + (b - a) * ∫ t in a..b, ‖deriv (N n) t‖ ^ 2)) =
        (fun n => 8 * C ^ 2 * L ^ 2 * delta n +
          (2 * C ^ 2 * (b - a)) * (delta n * ∫ t in a..b, ‖deriv (N n) t‖ ^ 2)) := by
      funext n
      ring
    rw [heq]
    simpa only [mul_zero, zero_add] using hh
  have herr : Tendsto err atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp herrsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using hh
  have hUd : ContinuousOn (deriv U) (Icc a b) := by
    intro t ht
    have hh := ((hU t ht).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
      (continuousAt_const (x := t) (y := (1 : ℝ)))
    simpa only [fderiv_apply_one_eq_deriv] using hh.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hUd
  let B0 := max B 0
  have hB0 : 0 ≤ B0 := le_max_right _ _
  have hBb (t : ℝ) (ht : t ∈ Icc a b) : ‖deriv U t‖ ≤ B0 :=
    (hB t ht).trans (le_max_left _ _)
  have hfixed : Tendsto (fun n => ∫ t in a..b, inner ℝ (deriv U t) (N n t)) atTop
      (𝓝 (∫ t in a..b, inner ℝ (deriv U t) (V t))) := by
    simp_rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => B0 * L)
    · intro n
      exact (hUd.inner (𝕜 := ℝ) (fun t ht =>
        (hN n t ht).continuousAt.continuousWithinAt)).aestronglyMeasurable measurableSet_Icc
    · exact continuousOn_const.integrableOn_compact isCompact_Icc
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hBb t ht) (hbound n t ht) (norm_nonneg _) hB0)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact tendsto_const_nhds.inner (hNlim t ht)
  have hh := herr.add hfixed
  simpa only [err, sub_add_cancel, zero_add] using hh

private theorem collar_point_tendsto {F : Type*} [TopologicalSpace F]
    {q : ℂ → F} {K : Set ℂ} (hq : ContinuousOn q K) {t : ℝ}
    (ht : (t : ℂ) ∈ K) {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0))
    (hmem : ∀ n, (t : ℂ) + (h n : ℂ) * I ∈ K) :
    Tendsto (fun n => q ((t : ℂ) + (h n : ℂ) * I)) atTop (𝓝 (q (t : ℂ))) := by
  have hm : Tendsto (fun n => (t : ℂ) + (h n : ℂ) * I) atTop (𝓝 (t : ℂ)) := by
    have hc := (continuous_ofReal.tendsto 0).comp hh
    simpa only [ofReal_zero, zero_mul, add_zero, Function.comp_def] using
      (tendsto_const_nhds (x := (t : ℂ))).add (hc.mul_const I)
  exact (hq (t : ℂ) ht).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hm, Eventually.of_forall hmem⟩)

private theorem horizontal_slice_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {q : ℂ → E} {t h : ℝ}
    (hq : DifferentiableAt ℝ q ((t : ℂ) + (h : ℂ) * I)) :
    deriv (fun s : ℝ => q ((s : ℂ) + (h : ℂ) * I)) t =
      fderiv ℝ q ((t : ℂ) + (h : ℂ) * I) 1 := by
  exact (hq.hasFDerivAt.comp_hasDerivAt t (ofRealCLM.hasDerivAt.add_const _)).deriv

private theorem continuousOn_deriv_of_c1 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {q : ℝ → E} {S : Set ℝ}
    (hq : ∀ t ∈ S, ContDiffAt ℝ 1 q t) : ContinuousOn (deriv q) S := by
  intro t ht
  have hh := ((hq t ht).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
    (continuousAt_const (x := t) (y := (1 : ℝ)))
  simpa only [fderiv_apply_one_eq_deriv] using hh.continuousWithinAt

theorem finite_weighted_connection_collar_limit {ι : Type*} [Finite ι] {n : ℕ}
    (g : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (D : ∀ i, LeviCivitaData (g i))
    (H T N : ι → ℂ → EuclideanSpace ℝ (Fin n)) (w : ι → ℂ → ℝ)
    {K U : ι → Set ℂ} (hK : ∀ i, IsCompact (K i))
    (hKU : ∀ i, UniqueDiffOn ℝ (K i)) (hU : ∀ i, IsOpen (U i))
    (hUK : ∀ i, U i ⊆ K i)
    (hH : ∀ i, ContDiffOn ℝ 1 (H i) (K i))
    (hw : ∀ i, ContDiffOn ℝ 1 (w i) (K i))
    (hT : ∀ i, ContinuousOn (T i) (K i))
    (hT1 : ∀ i, ContDiffOn ℝ 1 (T i) (U i))
    (hN : ∀ i, ContinuousOn (N i) (K i))
    (hN1 : ∀ i, ContDiffOn ℝ 1 (N i) (U i))
    (hDN : ∀ i, MemLp (fun z => fderiv ℝ (N i) z 1)
      2 (volume.restrict (K i ∩ U i)))
    (a b C : ι → ℝ) {delta : ℝ} (hd : 0 < delta)
    (hab : ∀ i, a i ≤ b i) (hC : ∀ i, 0 ≤ C i)
    (hrect : ∀ i, ∀ t ∈ Icc (a i) (b i), ∀ h ∈ Icc (0 : ℝ) delta,
      (t : ℂ) + (h : ℂ) * I ∈ K i)
    (hrectU : ∀ i, ∀ t ∈ Icc (a i) (b i), ∀ h ∈ Ioo (0 : ℝ) delta,
      (t : ℂ) + (h : ℂ) * I ∈ U i)
    (hT0 : ∀ i, ∀ t ∈ Icc (a i) (b i),
      ContDiffAt ℝ 1 (fun s : ℝ => T i (s : ℂ)) t)
    (hholder : ∀ i, ∀ z ∈ K i, ∀ y ∈ K i,
      ‖T i z - T i y‖ ≤ C i * Real.sqrt ‖z - y‖) :
    ∃ h : ℕ → ℝ, (∀ k, h k ∈ Ioo (0 : ℝ) delta) ∧ Tendsto h atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun k => ∫ t in (a i)..(b i),
        let z := (t : ℂ) + (h k : ℂ) * I
        w i z * (g i).inner (H i z)
          (covariantDerivativeAlongMap (D i) (H i) (T i) z 1) (N i z)) atTop
        (𝓝 (∫ t in (a i)..(b i), w i (t : ℂ) * (g i).inner (H i (t : ℂ))
          (deriv (fun s : ℝ => T i (s : ℂ)) t +
            connectionCoefficient (D i) (H i (t : ℂ))
              (fderivWithin ℝ (H i) (K i) (t : ℂ) 1) (T i (t : ℂ))) (N i (t : ℂ)))) := by
  classical
  let V := fun i => weightedMetricDual (g i) (H i) (N i) (w i)
  have hV (i : ι) := weightedMetricDual_regularity (g i) (hK i) (hKU i) (hU i)
    (hUK i) (hH i) (hw i) (hN i) (hN1 i) 1 (hDN i)
  have hzero (i : ι) (t : ℝ) (ht : t ∈ Icc (a i) (b i)) : (t : ℂ) ∈ K i := by
    simpa only [ofReal_zero, zero_mul, add_zero] using hrect i t ht 0 ⟨le_rfl, hd.le⟩
  have hsub (i : ι) : measurableEquivRealProd ⁻¹'
      (Icc (a i) (b i) ×ˢ Ioo (0 : ℝ) delta) ⊆ K i ∩ U i := by
    intro z hz
    have hu := hrectU i z.re hz.1 z.im hz.2
    rw [Complex.re_add_im] at hu
    exact ⟨hUK i hu, hu⟩
  have hDV (i : ι) : MemLp (fun z => fderiv ℝ (V i) z 1) 2 (volume.restrict
      (measurableEquivRealProd ⁻¹' (Icc (a i) (b i) ×ˢ Ioo (0 : ℝ) delta))) :=
    (hV i).2.2.mono_measure (Measure.restrict_mono (hsub i) le_rfl)
  obtain ⟨h, hgood, hlim, henergy⟩ := exists_common_collar_heights V a b hd hab
    (fun i h hh t ht => ((hV i).2.1.contDiffAt
      ((hU i).mem_nhds (hrectU i t ht h hh))).differentiableAt one_ne_zero)
    hDV (Good := fun _ => True) (Eventually.of_forall fun _ => trivial)
  have hh (k : ℕ) : h k ∈ Ioo (0 : ℝ) delta := (hgood k).1
  refine ⟨h, hh, hlim, ?_⟩
  intro i
  let J := Icc (a i) (b i)
  let z := fun (k : ℕ) (t : ℝ) => (t : ℂ) + (h k : ℂ) * I
  let Tk := fun k t => T i (z k t)
  let Vk := fun k t => V i (z k t)
  let T0 := fun t : ℝ => T i (t : ℂ)
  let V0 := fun t : ℝ => V i (t : ℂ)
  have hzK (k : ℕ) (t : ℝ) (ht : t ∈ J) : z k t ∈ K i :=
    hrect i t ht _ ⟨(hh k).1.le, (hh k).2.le⟩
  have hzU (k : ℕ) (t : ℝ) (ht : t ∈ J) : z k t ∈ U i := hrectU i t ht _ (hh k)
  have hzC (k : ℕ) : ContDiff ℝ 1 (z k) := ofRealCLM.contDiff.add contDiff_const
  have hTk (k : ℕ) (t : ℝ) (ht : t ∈ J) : ContDiffAt ℝ 1 (Tk k) t :=
    ((hT1 i).contDiffAt ((hU i).mem_nhds (hzU k t ht))).comp t (hzC k).contDiffAt
  have hVk (k : ℕ) (t : ℝ) (ht : t ∈ J) : ContDiffAt ℝ 1 (Vk k) t :=
    ((hV i).2.1.contDiffAt ((hU i).mem_nhds (hzU k t ht))).comp t (hzC k).contDiffAt
  obtain ⟨L, hL⟩ := (hK i).exists_bound_of_continuousOn (hV i).1
  let L0 := max L 0
  have hL0 : 0 ≤ L0 := le_max_right _ _
  have hVbound (k : ℕ) (t : ℝ) (ht : t ∈ J) : ‖Vk k t‖ ≤ L0 :=
    (hL _ (hzK k t ht)).trans (le_max_left _ _)
  have hTclose (k : ℕ) (t : ℝ) (ht : t ∈ J) :
      ‖Tk k t - T0 t‖ ≤ C i * Real.sqrt (h k) := by
    have hh' := hholder i _ (hzK k t ht) _ (hzero i t ht)
    simpa only [z, Tk, T0, add_sub_cancel_left, norm_mul, norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hh k).1] using hh'
  have hVlim (t : ℝ) (ht : t ∈ J) : Tendsto (fun k => Vk k t) atTop (𝓝 (V0 t)) :=
    collar_point_tendsto (hV i).1 (hzero i t ht) hlim (fun k => hzK k t ht)
  have hordinary := interval_flux_tendsto_of_pointwise (hab i) (hC i) hL0
    (fun k => (hh k).1.le) hlim hTk hVk (hT0 i) hTclose hVbound hVlim (henergy i)
  let A := fun z => w i z * (g i).inner (H i z)
    (connectionCoefficient (D i) (H i z) (fderivWithin ℝ (H i) (K i) z 1) (T i z)) (N i z)
  have hG : ContinuousOn (fun z => (g i).euclideanCoefficients (H i z)) (K i) :=
    (contDiff_iff_contDiffAt.mpr
      (g i).contDiffAt_euclideanCoefficients).continuous.comp_continuousOn (hH i).continuousOn
  have hDH : ContinuousOn (fun z => fderivWithin ℝ (H i) (K i) z 1) (K i) :=
    ((hH i).continuousOn_fderivWithin (hKU i) le_rfl).clm_apply continuousOn_const
  have hΓ : ContinuousOn (fun z => connectionCoefficient (D i) (H i z)) (K i) :=
    (contDiff_connectionCoefficient (D i)).continuous.comp_continuousOn (hH i).continuousOn
  have hA : ContinuousOn A (K i) :=
    (hw i).continuousOn.mul ((hG.clm_apply ((hΓ.clm_apply hDH).clm_apply (hT i))).clm_apply (hN i))
  have hAcurve (k : ℕ) : ContinuousOn (fun t => A (z k t)) J :=
    hA.comp (hzC k).continuous.continuousOn (hzK k)
  have hA0 : ContinuousOn (fun t : ℝ => A (t : ℂ)) J :=
    hA.comp continuous_ofReal.continuousOn (hzero i)
  obtain ⟨B, hB⟩ := (hK i).exists_bound_of_continuousOn hA
  have hcoefficient : Tendsto (fun k => ∫ t in (a i)..(b i), A (z k t)) atTop
      (𝓝 (∫ t in (a i)..(b i), A (t : ℂ))) := by
    simp_rw [intervalIntegral.integral_of_le (hab i), ← integral_Icc_eq_integral_Ioc]
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => B)
    · intro k
      exact (hAcurve k).aestronglyMeasurable measurableSet_Icc
    · exact continuousOn_const.integrableOn_compact isCompact_Icc
    · intro k
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hB _ (hzK k t ht)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact collar_point_tendsto hA (hzero i t ht) hlim (fun k => hzK k t ht)
  have hVkc (k : ℕ) : ContinuousOn (Vk k) J := fun t ht =>
    (hVk k t ht).continuousAt.continuousWithinAt
  have hV0 : ContinuousOn V0 J :=
    (hV i).1.comp continuous_ofReal.continuousOn (hzero i)
  have hsum := hordinary.add hcoefficient
  have hinterior (k : ℕ) :
      (∫ t in (a i)..(b i), inner ℝ (deriv (Tk k) t) (Vk k t)) +
        (∫ t in (a i)..(b i), A (z k t)) =
      ∫ t in (a i)..(b i), w i (z k t) * (g i).inner (H i (z k t))
        (covariantDerivativeAlongMap (D i) (H i) (T i) (z k t) 1) (N i (z k t)) := by
    rw [← intervalIntegral.integral_add
      (((continuousOn_deriv_of_c1 (hTk k)).inner
        (𝕜 := ℝ) (hVkc k)).intervalIntegrable_of_Icc (hab i))
      ((hAcurve k).intervalIntegrable_of_Icc (hab i))]
    apply intervalIntegral.integral_congr
    intro t ht
    have htJ : t ∈ J := by simpa only [J, uIcc_of_le (hab i)] using ht
    have hTd := ((hT1 i).contDiffAt ((hU i).mem_nhds (hzU k t htJ))).differentiableAt one_ne_zero
    have hderiv : deriv (Tk k) t = fderiv ℝ (T i) (z k t) 1 := horizontal_slice_deriv hTd
    dsimp only
    rw [hderiv, inner_weightedMetricDual]
    dsimp only [A, covariantDerivativeAlongMap]
    rw [fderivWithin_of_mem_nhds (mem_of_superset ((hU i).mem_nhds (hzU k t htJ)) (hUK i)),
      map_add, add_apply, mul_add]
  have hboundary :
      (∫ t in (a i)..(b i), inner ℝ (deriv T0 t) (V0 t)) +
        (∫ t in (a i)..(b i), A (t : ℂ)) =
      ∫ t in (a i)..(b i), w i (t : ℂ) * (g i).inner (H i (t : ℂ))
        (deriv T0 t + connectionCoefficient (D i) (H i (t : ℂ))
          (fderivWithin ℝ (H i) (K i) (t : ℂ) 1) (T i (t : ℂ))) (N i (t : ℂ)) := by
    rw [← intervalIntegral.integral_add
      (((continuousOn_deriv_of_c1 (hT0 i)).inner (𝕜 := ℝ) hV0).intervalIntegrable_of_Icc (hab i))
      (hA0.intervalIntegrable_of_Icc (hab i))]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only
    rw [inner_weightedMetricDual]
    simp only [A, T0, map_add, add_apply, mul_add]
  simp_rw [hinterior] at hsum
  rw [hboundary] at hsum
  exact hsum

end PoincareConjecture.M65Gauss
