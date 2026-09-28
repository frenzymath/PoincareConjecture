import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Transport.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Expansion








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData


def normalizedGradientDenominator (q : ℝ) : ℝ :=
  Real.smoothTransition (2 * q - 1) * q + (1 - Real.smoothTransition (2 * q - 1))

theorem normalizedGradientDenominator_eq {q : ℝ} (hq : 1 ≤ q) :
    normalizedGradientDenominator q = q := by
  simp only [normalizedGradientDenominator,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * q - 1),
    one_mul, sub_self, add_zero]

theorem normalizedGradientDenominator_ge (q : ℝ) :
    q ≤ normalizedGradientDenominator q := by
  by_cases hq : 1 ≤ q
  · rw [normalizedGradientDenominator_eq hq]
  · have hθ := Real.smoothTransition.le_one (2 * q - 1)
    dsimp [normalizedGradientDenominator]
    nlinarith

theorem normalizedGradientDenominator_lower (q : ℝ) :
    (1 / 2 : ℝ) ≤ normalizedGradientDenominator q := by
  by_cases hq : q ≤ 1 / 2
  · simp only [normalizedGradientDenominator,
      Real.smoothTransition.zero_of_nonpos (by linarith : 2 * q - 1 ≤ 0),
      zero_mul, sub_zero, zero_add]
    norm_num
  · exact (le_of_not_ge hq).trans (normalizedGradientDenominator_ge q)

theorem normalizedGradientDenominator_contDiff : ContDiff ℝ ∞ normalizedGradientDenominator := by
  exact ((Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul contDiff_id).add
      (contDiff_const.sub (Real.smoothTransition.contDiff.comp
        ((contDiff_const.mul contDiff_id).sub contDiff_const)))

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


def boundedNormalizedGradient (D : LeviCivitaData g) (f : M → ℝ) (x : M) :
    TangentSpace (𝓡 n) x :=
  (normalizedGradientDenominator
    (g.inner x (D.gradient f x) (D.gradient f x)))⁻¹ • D.gradient f x

theorem boundedNormalizedGradient_eq (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (hx : 1 ≤ g.inner x (D.gradient f x) (D.gradient f x)) :
    D.boundedNormalizedGradient f x = D.normalizedGradient f x := by
  simp only [boundedNormalizedGradient, normalizedGradient,
    normalizedGradientDenominator_eq hx]

theorem contMDiff_boundedNormalizedGradient (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (D.boundedNormalizedGradient f)) := by
  intro x
  have hq := (g.contMDiff_inner_gradient hf hf) x
  have hd := normalizedGradientDenominator_contDiff.contDiffAt.contMDiffAt.comp x hq
  have hpos : 0 < normalizedGradientDenominator
      (g.inner x (D.gradient f x) (D.gradient f x)) :=
    lt_of_lt_of_le (by norm_num) (normalizedGradientDenominator_lower _)
  exact ((contDiffAt_inv ℝ hpos.ne').contMDiffAt.comp x hd).smul_section
    (D.contMDiffAt_gradient (hf x))

theorem boundedNormalizedGradient_norm_le (D : LeviCivitaData g) (f : M → ℝ) (x : M) :
    g.tangentNorm x (D.boundedNormalizedGradient f x) ≤ 3 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let q := g.inner x (D.gradient f x) (D.gradient f x)
  let d := normalizedGradientDenominator q
  have hq : 0 ≤ q := by
    change 0 ≤ inner ℝ (D.gradient f x) (D.gradient f x)
    exact real_inner_self_nonneg
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) (normalizedGradientDenominator_lower q)
  have hs : Real.sqrt q ≤ q + 1 :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith [sq_nonneg q]⟩
  have hnum : Real.sqrt q ≤ 3 * d := by
    have h1 := normalizedGradientDenominator_ge q
    have h2 := normalizedGradientDenominator_lower q
    dsimp only [d]
    linarith
  change ‖d⁻¹ • D.gradient f x‖ ≤ 3
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  have hn : ‖D.gradient f x‖ = Real.sqrt q := by
    change _ = Real.sqrt (inner ℝ (D.gradient f x) (D.gradient f x))
    exact norm_eq_sqrt_real_inner (D.gradient f x)
  rw [hn, ← div_eq_inv_mul]
  exact (div_le_iff₀ hd).mpr hnum


theorem exists_complete_boundedNormalizedGradient_flow [T3Space M]
    (D : LeviCivitaData g) (hc : MetricComplete g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ∃ Φ : ℝ → M → M,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) (D.boundedNormalizedGradient f)) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ) :=
  g.exists_complete_flow_of_bounded_speed hc (D.boundedNormalizedGradient f)
    (D.contMDiff_boundedNormalizedGradient hf) (by norm_num : (0 : ℝ) ≤ 3)
    (D.boundedNormalizedGradient_norm_le f)

end PoincareConjecture.LeviCivitaData
