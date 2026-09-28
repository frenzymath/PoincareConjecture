import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedFiniteExceptions
import PoincareConjecture.Proofs.M65.Def18_23_Profile.AreaWeight

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

namespace PoincareConjecture.M65Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {a b : ℝ}

private theorem weightPrimitive_hasDerivWithinAt (F : RicciFlow 3 M (Icc a b))
    (compact : IsCompact (univ : Set M)) {q : ℝ} (hq : q ∈ Icc a b) :
    HasDerivWithinAt (fun q => ∫ r in a..q, m65AreaWeight F r)
      (m65AreaWeight F q) (Icc a b) q := by
  have hw := m65AreaWeight_continuousOn F compact
  have ha : a ∈ Icc a b := ⟨le_rfl, hq.1.trans hq.2⟩
  have : Fact (q ∈ Icc a b) := ⟨hq⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hw.mono (uIcc_subset_Icc ha hq)).intervalIntegrable)
    (hw.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc q) (hw q hq)

private theorem weighted_upperRight (F : RicciFlow 3 M (Icc a b))
    (compact : IsCompact (univ : Set M)) (A : ℝ → ℝ) (eta : ℝ)
    {q : ℝ} (hq : q ∈ Ioo a b)
    (hupper : ∀ delta : ℝ, 0 < delta → ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (A (q + h) - A q) / h ≤
        -2 * Real.pi - flowScalarCurvatureInfimum F q * A q / 2 + eta + delta) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ((m65WeightedArea F A (q + h) - eta * ∫ r in a..(q + h), m65AreaWeight F r) -
        (m65WeightedArea F A q - eta * ∫ r in a..q, m65AreaWeight F r)) / h ≤
          epsilon := by
  intro epsilon hepsilon
  let w := m65AreaWeight F
  let I := fun v => ∫ r in a..v, w r
  have hwpos : 0 < w q := m65AreaWeight_pos F q
  have hdw := (m65AreaWeight_hasDerivWithinAt F compact (Ioo_subset_Icc_self hq)).hasDerivAt
    (Icc_mem_nhds hq.1 hq.2)
  have hdI := (weightPrimitive_hasDerivWithinAt F compact
    (Ioo_subset_Icc_self hq)).hasDerivAt (Icc_mem_nhds hq.1 hq.2)
  have hshift : Tendsto (fun h : ℝ => q + h) (𝓝[>] (0 : ℝ)) (𝓝 q) := by
    have hc : ContinuousAt (fun h : ℝ => q + h) 0 := by fun_prop
    simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hw : Tendsto (fun h => w (q + h)) (𝓝[>] (0 : ℝ)) (𝓝 (w q)) :=
    hdw.continuousAt.tendsto.comp hshift
  have hwquot : Tendsto (fun h => (w (q + h) - w q) / h) (𝓝[>] (0 : ℝ))
      (𝓝 ((flowScalarCurvatureInfimum F q / 2) * w q)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hdw.tendsto_slope_zero_right
  have hIquot : Tendsto (fun h => (I (q + h) - I q) / h) (𝓝[>] (0 : ℝ))
      (𝓝 (w q)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hdI.tendsto_slope_zero_right
  let delta := epsilon / (2 * w q)
  have hdelta : 0 < delta := div_pos hepsilon (mul_pos (by norm_num) hwpos)
  let d := -2 * Real.pi - flowScalarCurvatureInfimum F q * A q / 2 + eta + delta
  let G := fun h => w (q + h) * d + (w (q + h) - w q) / h * A q +
    (2 * Real.pi - eta) * ((I (q + h) - I q) / h)
  have hG : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (epsilon / 2)) := by
    have hlim : Tendsto G (𝓝[>] (0 : ℝ))
        (𝓝 (w q * d + ((flowScalarCurvatureInfimum F q / 2) * w q) * A q +
          (2 * Real.pi - eta) * w q)) :=
      ((hw.mul_const d).add (hwquot.mul_const (A q))).add
        (hIquot.const_mul (2 * Real.pi - eta))
    have heq : w q * d + ((flowScalarCurvatureInfimum F q / 2) * w q) * A q +
        (2 * Real.pi - eta) * w q = epsilon / 2 := by
      dsimp only [d, delta]
      field_simp [hwpos.ne']
      ring
    simpa only [heq] using hlim
  filter_upwards [hupper delta hdelta,
    hG.eventually (Iio_mem_nhds (show epsilon / 2 < epsilon by linarith))] with h hh hGh
  have hmul : w (q + h) * ((A (q + h) - A q) / h) ≤ w (q + h) * d :=
    mul_le_mul_of_nonneg_left hh (m65AreaWeight_pos F (q + h)).le
  calc
    _ = w (q + h) * ((A (q + h) - A q) / h) +
        (w (q + h) - w q) / h * A q +
          (2 * Real.pi - eta) * ((I (q + h) - I q) / h) := by
      dsimp only [m65WeightedArea, I, w]
      ring
    _ ≤ G h := by dsimp only [G]; linarith
    _ ≤ epsilon := hGh.le

theorem weighted_comparison_finite (F : RicciFlow 3 M (Icc a b))
    (compact : IsCompact (univ : Set M)) (A : ℝ → ℝ) (eta : ℝ) (E : Finset ℝ)
    {s t : ℝ} (hst : s ≤ t) (hsub : Icc s t ⊆ Ioo a b)
    (hA : ContinuousOn A (Icc s t))
    (hupper : ∀ q ∈ Ioo s t, q ∉ E → ∀ delta : ℝ, 0 < delta →
      ∀ᶠ h in 𝓝[>] (0 : ℝ), (A (q + h) - A q) / h ≤
        -2 * Real.pi - flowScalarCurvatureInfimum F q * A q / 2 + eta + delta) :
    m65WeightedArea F A t - eta * (∫ r in a..t, m65AreaWeight F r) ≤
      m65WeightedArea F A s - eta * (∫ r in a..s, m65AreaWeight F r) := by
  let Z := fun q => m65WeightedArea F A q - eta * ∫ r in a..q, m65AreaWeight F r
  have hI : ContinuousOn (fun q => ∫ r in a..q, m65AreaWeight F r) (Icc a b) :=
    fun q hq => (weightPrimitive_hasDerivWithinAt F compact hq).continuousWithinAt
  have hw := (m65AreaWeight_continuousOn F compact).mono
    (hsub.trans Ioo_subset_Icc_self)
  have hIp := hI.mono (hsub.trans Ioo_subset_Icc_self)
  have hZ : ContinuousOn Z (Icc s t) :=
    ((hw.mul hA).add (continuousOn_const.mul hIp)).sub (continuousOn_const.mul hIp)
  exact nonincrease_of_upperRight_finite Z E hst hZ (fun q hq hnot =>
    weighted_upperRight F compact A eta (hsub (Ioo_subset_Icc_self hq)) (hupper q hq hnot))

theorem weighted_difference_profile (F : RicciFlow 3 M (Icc a b))
    (A : ℝ → ℝ) (s t : ℝ) :
    m65WeightedArea F A t - m65WeightedArea F A s =
      m65AreaWeight F t * (A t - m65RestartedAreaProfile F s (A s) t) := by
  let P := fun q => ∫ r in a..q, flowScalarCurvatureInfimum F r / 2
  have hexp : m65AreaWeight F t * Real.exp (P s - P t) = m65AreaWeight F s := by
    dsimp only [m65AreaWeight, P]
    rw [← Real.exp_add]
    congr 1
    ring
  have ht := m65WeightedArea_profile_error F A 0 t
  have hs := m65WeightedArea_profile_error F A 0 s
  have hp := m65RestartedAreaProfile_difference F s (A s) 0 t
  calc
    _ = m65AreaWeight F t * (A t - areaComparisonProfile F 0 t) -
        m65AreaWeight F s * (A s - areaComparisonProfile F 0 s) := by linarith
    _ = m65AreaWeight F t * (A t - areaComparisonProfile F 0 t) -
        m65AreaWeight F t * (Real.exp (P s - P t) *
          (A s - areaComparisonProfile F 0 s)) := by rw [← mul_assoc, hexp]
    _ = _ := by rw [← hp]; ring

end PoincareConjecture.M65Perturbation
