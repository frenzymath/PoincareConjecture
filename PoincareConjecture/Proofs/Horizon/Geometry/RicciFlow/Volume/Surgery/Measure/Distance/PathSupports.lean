import PoincareConjecture.Proofs.M10.PathSupports
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.Distance.CurveCalculus
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.Distance.SupportIntegral



















set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SurgeryVolume.Measure

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {γ : ℝ → M}


theorem sub_le_integral_speed_of_upper_supports
    (g : RiemannianMetric n M) {f : M → ℝ} {U : Set M}
    (hf : ContinuousOn f U) {C : ℝ}
    (hsupport : ∀ q ∈ U, ∃ B : M → ℝ,
      MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) B q ∧ B q = f q ∧
        (∀ᶠ x in 𝓝 q, f x ≤ B x) ∧ ∀ v : TangentSpace (𝓡 n) q,
          |mvfderiv (𝓡 n) B q v| ≤ C * g.tangentNorm q v)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ) {a b : ℝ} (hab : a ≤ b)
    (hγU : MapsTo γ (Icc a b) U) :
    f (γ b) - f (γ a) ≤ C * ∫ t in a..b, g.tangentNorm (γ t) (curveVelocity γ t) := by
  have h := sub_le_integral_of_upper_supports (f := f ∘ γ)
    (h := fun t ↦ C * g.tangentNorm (γ t) (curveVelocity γ t)) hab
    (hf.comp hγ.continuous.continuousOn hγU)
    (continuous_const.mul (continuous_tangentNorm_curveVelocity g hγ)) (fun t ht ↦ ?_)
  · simpa only [Function.comp_apply, intervalIntegral.integral_const_mul] using h
  obtain ⟨B, hB, htouch, hdom, hbound⟩ := hsupport (γ t) (hγU (Ico_subset_Icc_self ht))
  refine ⟨B ∘ γ, mvfderiv (𝓡 n) B (γ t) (curveVelocity γ t),
    hasDerivAt_comp_curve hB (hγ.mdifferentiable one_ne_zero t), htouch,
    hγ.continuous.continuousAt hdom, ?_⟩
  exact (le_abs_self _).trans (hbound _)


theorem ofReal_sub_le_pathELength_of_upper_supports
    (g : RiemannianMetric n M) {f : M → ℝ} {U : Set M}
    (hf : ContinuousOn f U) {C : ℝ} (hC : 0 ≤ C)
    (hsupport : ∀ q ∈ U, ∃ B : M → ℝ,
      MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) B q ∧ B q = f q ∧
        (∀ᶠ x in 𝓝 q, f x ≤ B x) ∧ ∀ v : TangentSpace (𝓡 n) q,
          |mvfderiv (𝓡 n) B q v| ≤ C * g.tangentNorm q v)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ) {a b : ℝ} (hab : a ≤ b)
    (hγU : MapsTo γ (Icc a b) U) :
    ENNReal.ofReal (f (γ b) - f (γ a)) ≤ ENNReal.ofReal C * g.pathELength γ a b := by
  have h := ENNReal.ofReal_le_ofReal
    (sub_le_integral_speed_of_upper_supports g hf hsupport hγ hab hγU)
  rwa [ENNReal.ofReal_mul hC, ← pathELength_eq_ofReal_integral_tangentNorm g hγ hab] at h


theorem pathELength_reverse_unit (g : RiemannianMetric n M)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ) :
    g.pathELength (γ ∘ fun t : ℝ ↦ 1 - t) 0 1 = g.pathELength γ 0 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  delta RiemannianMetric.pathELength
  simpa only [sub_self, sub_zero] using
    (Manifold.pathELength_comp_of_antitoneOn (I := 𝓡 n) (γ := γ)
      (f := fun t : ℝ ↦ 1 - t) zero_le_one
      (fun _ _ _ _ h ↦ sub_le_sub_left h 1)
      ((differentiable_const (1 : ℝ)).sub differentiable_id).differentiableOn
      (hγ.mdifferentiable one_ne_zero).mdifferentiableOn)


theorem edist_le_pathELength_of_upper_supports
    (g : RiemannianMetric n M) {f : M → ℝ} {U : Set M}
    (hf : ContinuousOn f U) {C : ℝ} (hC : 0 ≤ C)
    (hsupport : ∀ q ∈ U, ∃ B : M → ℝ,
      MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) B q ∧ B q = f q ∧
        (∀ᶠ x in 𝓝 q, f x ≤ B x) ∧ ∀ v : TangentSpace (𝓡 n) q,
          |mvfderiv (𝓡 n) B q v| ≤ C * g.tangentNorm q v)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ)
    (hγU : MapsTo γ (Icc 0 1) U) :
    edist (f (γ 0)) (f (γ 1)) ≤ ENNReal.ofReal C * g.pathELength γ 0 1 := by
  have hforward := ofReal_sub_le_pathELength_of_upper_supports g hf hC hsupport hγ
    zero_le_one hγU
  have hreverse : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 (γ ∘ fun t : ℝ ↦ 1 - t) :=
    hγ.comp ((contMDiff_const.sub contMDiff_id) :
      ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1 (fun t : ℝ ↦ 1 - t))
  have hreverseU : MapsTo (γ ∘ fun t : ℝ ↦ 1 - t) (Icc 0 1) U := by
    intro t ht
    apply hγU
    constructor <;> linarith [ht.1, ht.2]
  have hback := ofReal_sub_le_pathELength_of_upper_supports g hf hC hsupport hreverse
    zero_le_one hreverseU
  rw [pathELength_reverse_unit g hγ] at hback
  simp only [Function.comp_apply, sub_self, sub_zero] at hback
  rw [edist_dist, Real.dist_eq, abs_eq_max_neg, ENNReal.ofReal_max, neg_sub]
  exact max_le hback hforward

end PoincareConjecture.SurgeryVolume.Measure
