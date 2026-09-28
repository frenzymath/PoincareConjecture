import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Flow.BoundedSpeed
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def boundedFieldScale (g : RiemannianMetric n M)
    (X : (x : M) → TangentSpace (𝓡 n) x) (x : M) : ℝ :=
  (1 + g.inner x (X x) (X x))⁻¹

theorem boundedFieldScale_pos (g : RiemannianMetric n M)
    (X : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    0 < g.boundedFieldScale X x := by
  have hinner : 0 ≤ g.inner x (X x) (X x) := by
    by_cases h : X x = 0
    · simp [h]
    · exact (g.pos x (X x) h).le
  exact inv_pos.mpr (by linarith)

theorem contMDiff_boundedFieldScale (g : RiemannianMetric n M)
    {X : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (g.boundedFieldScale X) := by
  intro x
  have hi := ((g.contMDiff x).clm_bundle_apply (hX x)).clm_bundle_apply (hX x)
  have he : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (X y) (X y)) x := by
    simpa using (contMDiffAt_totalSpace.mp hi).2
  have hne : 1 + g.inner x (X x) (X x) ≠ 0 := by
    intro hz
    have hp := g.boundedFieldScale_pos X x
    simp only [boundedFieldScale, hz, inv_zero, lt_self_iff_false] at hp
  exact ((contDiffAt_inv ℝ hne).contMDiffAt.comp x
    (contMDiffAt_const.add he))

theorem tangentNorm_boundedField_le_one (g : RiemannianMetric n M)
    (X : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    g.tangentNorm x (g.boundedFieldScale X x • X x) ≤ 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change ‖g.boundedFieldScale X x • X x‖ ≤ 1
  rw [norm_smul, Real.norm_of_nonneg (g.boundedFieldScale_pos X x).le]
  change (1 + inner ℝ (X x) (X x))⁻¹ * ‖X x‖ ≤ 1
  rw [real_inner_self_eq_norm_sq, ← div_eq_inv_mul]
  apply (div_le_one (by positivity : 0 < 1 + ‖X x‖ ^ 2)).mpr
  nlinarith [sq_nonneg (‖X x‖ - 1)]

theorem exists_smooth_globalFlow_of_positive_rescaling [T3Space M]
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {X : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X)) :
    ∃ Φ : ℝ → M → M,
      (∀ x, Φ 0 x = x) ∧
      (∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x)
        (fun y => g.boundedFieldScale X y • X y)) ∧
      (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ) := by
  apply g.exists_smooth_globalFlow_of_bounded_speed hc
    (fun x => ((g.contMDiff_boundedFieldScale hX) x).smul_section (hX x))
    zero_le_one
  exact g.tangentNorm_boundedField_le_one X

end PoincareConjecture.RiemannianMetric
