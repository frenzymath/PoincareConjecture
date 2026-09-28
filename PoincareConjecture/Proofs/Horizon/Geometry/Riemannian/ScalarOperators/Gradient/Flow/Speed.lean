import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Expansion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CurveLength

set_option autoImplicit false

open Set Filter MeasureTheory
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Bundle Topology
namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem tangentNorm_normalizedGradient_le
    (D : LeviCivitaData g) (f : M → ℝ) (x : M) {l : ℝ} (hl : 0 < l)
    (hgrad : l ≤ g.tangentNorm x (D.gradient f x)) :
    g.tangentNorm x (D.normalizedGradient f x) ≤ 1 / l := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hn : 0 < ‖D.gradient f x‖ := hl.trans_le hgrad
  change ‖(inner ℝ (D.gradient f x) (D.gradient f x))⁻¹ • D.gradient f x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, real_inner_self_eq_norm_sq,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  calc
    (‖D.gradient f x‖ ^ 2)⁻¹ * ‖D.gradient f x‖ = 1 / ‖D.gradient f x‖ := by
      field_simp
    _ ≤ 1 / l := div_le_div_of_nonneg_left zero_le_one hl hgrad

theorem edist_le_of_normalizedGradient_curve
    (D : LeviCivitaData g) {f : M → ℝ} {γ : ℝ → M}
    {I : Set ℝ} (hI : IsOpen I)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    (horbit : IsMIntegralCurveOn (I := 𝓡 n) γ (D.normalizedGradient f) I)
    {l a b : ℝ} (hl : 0 < l) (hab : a ≤ b) (hsub : Icc a b ⊆ I)
    (hgrad : ∀ t ∈ I, l ≤ g.tangentNorm (γ t) (D.gradient f (γ t))) :
    g.edist (γ a) (γ b) ≤ ENNReal.ofReal ((b - a) / l) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hspeed := g.continuousOn_speed_of_contMDiffOn hI hγ
  have h := g.edist_le_ofReal_integral_speed hab ((hγ.mono hsub).of_le (by simp))
    (hspeed.mono hsub)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) ≤ 1 / l := by
    have hd := (horbit.isMIntegralCurveAt (hI.mem_nhds (hsub ht))).hasMFDerivAt.mfderiv
    rw [hd]
    change g.tangentNorm (γ t) ((1 : ℝ) • D.normalizedGradient f (γ t)) ≤ 1 / l
    rw [one_smul]
    exact D.tangentNorm_normalizedGradient_le f (γ t) hl (hgrad t (hsub ht))
  have hi := intervalIntegral.integral_mono_on hab
    ((hspeed.mono hsub).intervalIntegrable_of_Icc hab)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 1 / l) volume a b) hbound
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] using hi
end PoincareConjecture.LeviCivitaData
