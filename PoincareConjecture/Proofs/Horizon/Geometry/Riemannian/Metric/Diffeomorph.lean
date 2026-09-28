import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic
import Mathlib.Geometry.Manifold.Diffeomorph










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]



theorem pathELength_diffeomorph
    (gM : RiemannianMetric n M) (gN : RiemannianMetric n N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w))
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) (a b : ℝ) :
    gM.pathELength γ a b = gN.pathELength (e ∘ γ) a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨gM.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨gN.toRiemannianMetric⟩
  unfold pathELength
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc,
    Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr
  intro t
  rw [mfderiv_comp t (e.mdifferentiable (by simp) (γ t))
    (hγ.mdifferentiable one_ne_zero t)]
  simp only [enorm_eq_nnnorm, ENNReal.coe_inj]
  apply NNReal.eq
  change ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1‖ =
    ‖mfderiv (𝓡 n) (𝓡 n) e (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)‖
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  exact congrArg Real.sqrt (hinner (γ t) _ _)



theorem edist_diffeomorph
    (gM : RiemannianMetric n M) (gN : RiemannianMetric n N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w))
    (x y : M) : gM.edist x y = gN.edist (e x) (e y) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨gM.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨gN.toRiemannianMetric⟩
  apply le_antisymm
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
    have hγM : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (e.symm ∘ γ) :=
      (e.symm.contMDiff.of_le (by simp)).comp hγ
    have hle : gM.edist x y ≤ gM.pathELength (e.symm ∘ γ) 0 1 :=
      Manifold.riemannianEDist_le_pathELength hγM.contMDiffOn
        (by simp [h0]) (by simp [h1]) zero_le_one
    rw [pathELength_diffeomorph gM gN e hinner (e.symm ∘ γ) hγM] at hle
    have heq : e ∘ (e.symm ∘ γ) = γ := by funext s; simp
    rw [heq] at hle
    exact hle.trans_lt hlen
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
    have hγN : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (e ∘ γ) :=
      (e.contMDiff.of_le (by simp)).comp hγ
    have hle : gN.edist (e x) (e y) ≤ gN.pathELength (e ∘ γ) 0 1 :=
      Manifold.riemannianEDist_le_pathELength hγN.contMDiffOn
        (congrArg e h0) (congrArg e h1) zero_le_one
    rw [← pathELength_diffeomorph gM gN e hinner γ hγ] at hle
    exact hle.trans_lt hlen



theorem image_ball_diffeomorph
    (gM : RiemannianMetric n M) (gN : RiemannianMetric n N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w))
    (x : M) (r : ℝ) : e '' gM.ball x r = gN.ball (e x) r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [ball, mem_ofPred_eq, edist_diffeomorph gM gN e hinner] using hz
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    simpa only [ball, mem_ofPred_eq, edist_diffeomorph gM gN e hinner,
      e.apply_symm_apply] using hy



theorem metricComplete_iff_diffeomorph [T3Space M] [T3Space N]
    (gM : RiemannianMetric n M) (gN : RiemannianMetric n N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w)) :
    MetricComplete gM ↔ MetricComplete gN := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨gM.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨gM.inner, gM.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let mM : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨gN.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨⟨gN.inner, gN.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let mN : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
  let ei : M ≃ᵢ N :=
    { e.toEquiv with
      isometry_toFun := fun x y => (edist_diffeomorph gM gN e hinner x y).symm }
  exact ei.completeSpace_iff



theorem volumeMeasure_image_diffeomorph [T3Space M] [T3Space N]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
    (gM : RiemannianMetric n M) (gN : RiemannianMetric n N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w))
    (s : Set M) : gN.volumeMeasure (e '' s) = gM.volumeMeasure s := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨gM.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨gM.inner, gM.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let mM : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨gN.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨⟨gN.inner, gN.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let mN : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
  have hi : @Isometry M N mM.toPseudoEMetricSpace mN.toPseudoEMetricSpace e :=
    fun x y => (edist_diffeomorph gM gN e hinner x y).symm
  exact @Isometry.euclideanHausdorffMeasure_image M N mM _ _ mN _ _ e n hi s



theorem volumeMeasure_ball_diffeomorph [T3Space M] [T3Space N]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
    (gM : RiemannianMetric n M) (gN : RiemannianMetric n N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w))
    (x : M) (r : ℝ) :
    gM.volumeMeasure (gM.ball x r) = gN.volumeMeasure (gN.ball (e x) r) := by
  rw [← image_ball_diffeomorph gM gN e hinner x r]
  exact (volumeMeasure_image_diffeomorph gM gN e hinner _).symm

end PoincareConjecture.RiemannianMetric
