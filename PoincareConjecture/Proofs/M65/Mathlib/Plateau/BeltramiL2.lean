import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.MetricSpace.Contracting

set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform Filter
open scoped Topology ENNReal NNReal ComplexConjugate

namespace Complex

private def multiplierL2 (a : ℂ → ℂ) (ha : AEStronglyMeasurable a volume)
    (C : ℝ) (hC : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) :
    Lp ℂ 2 (volume : Measure ℂ) →L[ℝ] Lp ℂ 2 (volume : Measure ℂ) :=
  Lp.coefficientL2 (fun z => ContinuousLinearMap.mul ℝ ℂ (a z))
    ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp_aestronglyMeasurable ha)
    C (hC.mono fun z hz => (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ (a z)).trans hz)

private theorem multiplierL2_ae (a : ℂ → ℂ) (ha : AEStronglyMeasurable a volume)
    (C : ℝ) (hC : ∀ᵐ z ∂volume, ‖a z‖ ≤ C)
    (u : Lp ℂ 2 (volume : Measure ℂ)) :
    multiplierL2 a ha C hC u =ᵐ[volume] fun z => a z * u z :=
  Lp.coefficientL2_ae _ _ _ _ u

private theorem norm_multiplierL2_le (a : ℂ → ℂ)
    (ha : AEStronglyMeasurable a volume) (C : ℝ)
    (hC : ∀ᵐ z ∂volume, ‖a z‖ ≤ C) (u : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖multiplierL2 a ha C hC u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplierL2_ae a ha C hC u, hC] with z hz hbound
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

private theorem measurable_beurlingSymbol :
    Measurable (fun z : ℂ => conj z / z) := by fun_prop

private theorem norm_beurlingSymbol_le (z : ℂ) : ‖conj z / z‖ ≤ 1 := by
  rw [norm_div, norm_conj]
  by_cases hz : z = 0
  · simp [hz]
  · simp [norm_ne_zero_iff.mpr hz]

def beurlingL2 : Lp ℂ 2 (volume : Measure ℂ) →L[ℝ] Lp ℂ 2 (volume : Measure ℂ) :=
  let F := (Lp.fourierTransformₗᵢ ℂ ℂ).toContinuousLinearEquiv
  (F.symm.toContinuousLinearMap.restrictScalars ℝ).comp
    ((multiplierL2 (fun z => conj z / z) measurable_beurlingSymbol.aestronglyMeasurable
      1 (Eventually.of_forall norm_beurlingSymbol_le)).comp
        (F.toContinuousLinearMap.restrictScalars ℝ))

theorem fourier_beurlingL2_ae (u : Lp ℂ 2 (volume : Measure ℂ)) :
    (𝓕 (beurlingL2 u) : Lp ℂ 2 (volume : Measure ℂ)) =ᵐ[volume]
      fun z => (conj z / z) * (𝓕 u : Lp ℂ 2 (volume : Measure ℂ)) z := by
  change (Lp.fourierTransformₗᵢ ℂ ℂ)
    ((Lp.fourierTransformₗᵢ ℂ ℂ).symm (multiplierL2 (fun z => conj z / z)
      measurable_beurlingSymbol.aestronglyMeasurable 1
      (Eventually.of_forall norm_beurlingSymbol_le) (𝓕 u))) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact multiplierL2_ae _ _ _ _ _

theorem norm_beurlingL2_le (u : Lp ℂ 2 (volume : Measure ℂ)) :
    ‖beurlingL2 u‖ ≤ ‖u‖ := by
  change ‖(Lp.fourierTransformₗᵢ ℂ ℂ).symm (multiplierL2 (fun z => conj z / z)
    measurable_beurlingSymbol.aestronglyMeasurable 1
    (Eventually.of_forall norm_beurlingSymbol_le) (𝓕 u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa using norm_multiplierL2_le (fun z => conj z / z)
    measurable_beurlingSymbol.aestronglyMeasurable 1
    (Eventually.of_forall norm_beurlingSymbol_le) (𝓕 u)

theorem existsUnique_beltramiL2 {μ : ℂ → ℂ}
    (hμ : AEStronglyMeasurable μ volume) {k : ℝ≥0} (hk : k < 1)
    (hbound : ∀ᵐ z ∂volume, ‖μ z‖ ≤ (k : ℝ))
    (a : Lp ℂ 2 (volume : Measure ℂ)) :
    ∃! h : Lp ℂ 2 (volume : Measure ℂ),
      (∀ᵐ z ∂volume, h z = μ z * beurlingL2 h z + a z) ∧
      ‖h‖ ≤ ‖a‖ / (1 - (k : ℝ)) := by
  let T := (multiplierL2 μ hμ k hbound).comp beurlingL2
  have hT (h : Lp ℂ 2 (volume : Measure ℂ)) : ‖T h‖ ≤ (k : ℝ) * ‖h‖ :=
    (norm_multiplierL2_le μ hμ k hbound (beurlingL2 h)).trans
      (mul_le_mul_of_nonneg_left (norm_beurlingL2_le h) k.coe_nonneg)
  let F := fun h : Lp ℂ 2 (volume : Measure ℂ) => T h + a
  have hF : ContractingWith k F := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    simpa only [F, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub] using hT (u - v)
  let h := hF.fixedPoint F
  have hfix : T h + a = h := hF.fixedPoint_isFixedPt
  have hae : ∀ᵐ z ∂volume, h z = μ z * beurlingL2 h z + a z := by
    filter_upwards [Lp.coeFn_add (T h) a,
      multiplierL2_ae μ hμ k hbound (beurlingL2 h)] with z hz hmul
    calc
      h z = (T h + a) z := congrArg (fun v : Lp ℂ 2 (volume : Measure ℂ) => v z)
        hfix.symm
      _ = _ := hz.trans (congrArg (fun v => v + a z) hmul)
  have hnorm : ‖h‖ ≤ ‖a‖ / (1 - (k : ℝ)) := by
    have hlt : (k : ℝ) < 1 := hk
    apply (le_div_iff₀ (by linarith : 0 < 1 - (k : ℝ))).mpr
    have hn : ‖h‖ ≤ (k : ℝ) * ‖h‖ + ‖a‖ := by
      calc
        ‖h‖ = ‖T h + a‖ := congrArg norm hfix.symm
        _ ≤ ‖T h‖ + ‖a‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (hT h) le_rfl
    nlinarith
  refine ⟨h, ⟨hae, hnorm⟩, fun v hv => ?_⟩
  apply hF.fixedPoint_unique
  apply Lp.ext
  filter_upwards [hv.1, Lp.coeFn_add (T v) a,
    multiplierL2_ae μ hμ k hbound (beurlingL2 v)] with z hz hsum hmul
  change (T v + a) z = v z
  rw [hsum]
  exact (congrArg (fun w => w + a z) hmul).trans hz.symm

end Complex
