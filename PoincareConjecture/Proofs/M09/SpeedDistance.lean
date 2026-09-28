import PoincareConjecture.Proofs.M09.RiemannianProper
import PoincareConjecture.Definitions.Ch06.LGeometry








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal NNReal
open MeasureTheory

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem pathELength_le_of_speed_le (g : RiemannianMetric n M) (γ : ℝ → M)
    (a b C : ℝ) (hC : 0 ≤ C)
    (hspeed : ∀ s ∈ Set.Icc a b, g.tangentNorm (γ s) (curveVelocity γ s) ≤ C) :
    g.pathELength γ a b ≤ ENNReal.ofReal (C * (b - a)) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 n) γ a b ≤ _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  calc
    _ ≤ ∫⁻ _ in Set.Icc a b, ENNReal.ofReal C := by
      apply setLIntegral_mono measurable_const
      intro s hs
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_eq_sqrt_real_inner]
      exact hspeed s hs
    _ = _ := by rw [setLIntegral_const, Real.volume_Icc, ENNReal.ofReal_mul hC]

theorem riemannianEDist_le_of_speed_le (g : RiemannianMetric n M) (γ : ℝ → M)
    (a b C : ℝ) (hab : a ≤ b) (hC : 0 ≤ C)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Set.Icc a b))
    (hspeed : ∀ s ∈ Set.Icc a b, g.tangentNorm (γ s) (curveVelocity γ s) ≤ C) :
    g.edist (γ a) (γ b) ≤ ENNReal.ofReal (C * (b - a)) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab).trans
    (pathELength_le_of_speed_le g γ a b C hC hspeed)

theorem selectedMetric_dist_le_of_speed_le [T3Space M] [ConnectedSpace M]
    (g : RiemannianMetric n M) (γ : ℝ → M) (a b C : ℝ) (hab : a ≤ b) (hC : 0 ≤ C)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Set.Icc a b))
    (hspeed : ∀ s ∈ Set.Icc a b, g.tangentNorm (γ s) (curveVelocity γ s) ≤ C) :
    letI : MetricSpace M := selectedMetricSpace g
    dist (γ a) (γ b) ≤ C * (b - a) := by
  letI : MetricSpace M := selectedMetricSpace g
  have h := riemannianEDist_le_of_speed_le g γ a b C hab hC hγ hspeed
  rw [← selectedMetricSpace_edist, edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sub_nonneg.mpr hab))).mp h

theorem selectedMetric_lipschitzOn_of_speed_le [T3Space M] [ConnectedSpace M]
    (g : RiemannianMetric n M) (γ : ℝ → M) (a b : ℝ) (C : ℝ≥0)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Set.Icc a b))
    (hspeed : ∀ s ∈ Set.Icc a b, g.tangentNorm (γ s) (curveVelocity γ s) ≤ C) :
    letI : MetricSpace M := selectedMetricSpace g
    LipschitzOnWith C γ (Set.Icc a b) := by
  letI : MetricSpace M := selectedMetricSpace g
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · have hsub : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2
    have h := selectedMetric_dist_le_of_speed_le g γ x y C hxy C.property
      (hγ.mono hsub) (fun s hs ↦ hspeed s (hsub hs))
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub] using h
  · have hsub : Set.Icc y x ⊆ Set.Icc a b := Set.Icc_subset_Icc hy.1 hx.2
    have h := selectedMetric_dist_le_of_speed_le g γ y x C hyx C.property
      (hγ.mono hsub) (fun s hs ↦ hspeed s (hsub hs))
    simpa only [dist_comm (γ x), Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)] using h

end PoincareConjecture.Proofs.M09
