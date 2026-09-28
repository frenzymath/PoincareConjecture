import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Immersion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]


theorem pathELength_map_of_metric_pullback
    (gM : RiemannianMetric n M) (gN : RiemannianMetric m N) {F : M → N}
    (hF : ContMDiff (𝓡 n) (𝓡 m) ∞ F)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (F x)
        (mfderiv (𝓡 n) (𝓡 m) F x v) (mfderiv (𝓡 n) (𝓡 m) F x w))
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) (a b : ℝ) :
    gM.pathELength γ a b = gN.pathELength (F ∘ γ) a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨gM.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : N → Type _) := ⟨gN.toRiemannianMetric⟩
  unfold pathELength
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc,
    Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr
  intro t
  rw [mfderiv_comp t (hF.mdifferentiable (by simp) (γ t))
    (hγ.mdifferentiable one_ne_zero t)]
  simp only [enorm_eq_nnnorm, ENNReal.coe_inj]
  apply NNReal.eq
  change ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1‖ =
    ‖mfderiv (𝓡 n) (𝓡 m) F (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)‖
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  exact congrArg Real.sqrt (hinner (γ t) _ _)


theorem edist_map_le_of_metric_pullback
    (gM : RiemannianMetric n M) (gN : RiemannianMetric m N) {F : M → N}
    (hF : ContMDiff (𝓡 n) (𝓡 m) ∞ F)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (F x)
        (mfderiv (𝓡 n) (𝓡 m) F x v) (mfderiv (𝓡 n) (𝓡 m) F x w))
    (x y : M) : gN.edist (F x) (F y) ≤ gM.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨gM.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : N → Type _) := ⟨gN.toRiemannianMetric⟩
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, h0, h1, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
  have hle : gN.edist (F x) (F y) ≤ gN.pathELength (F ∘ γ) 0 1 :=
    Manifold.riemannianEDist_le_pathELength
      ((hF.of_le (by simp)).comp hγ).contMDiffOn
      (congrArg F h0) (congrArg F h1) zero_le_one
  rw [← pathELength_map_of_metric_pullback gM gN hF hinner γ hγ] at hle
  exact hle.trans_lt hlen



theorem metricComplete_of_isClosedEmbedding [T3Space M] [T3Space N]
    (gM : RiemannianMetric n M) (gN : RiemannianMetric m N) {F : M → N}
    (hF : ContMDiff (𝓡 n) (𝓡 m) ∞ F) (hemb : Topology.IsClosedEmbedding F)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      gM.inner x v w = gN.inner (F x)
        (mfderiv (𝓡 n) (𝓡 m) F x v) (mfderiv (𝓡 n) (𝓡 m) F x w))
    (hc : MetricComplete gN) : MetricComplete gM := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨gM.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨gM.inner, gM.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  letI mM : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : N → Type _) := ⟨gN.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin m))
      (TangentSpace (𝓡 m) : N → Type _) :=
    ⟨⟨gN.inner, gN.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  letI mN : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 m) N
  let : CompleteSpace N := hc
  have hLip : LipschitzWith 1 F := by
    intro x y
    change gN.edist (F x) (F y) ≤ (1 : ℝ≥0∞) * gM.edist x y
    simpa only [one_mul] using
      edist_map_le_of_metric_pullback gM gN hF hinner x y
  apply EMetric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (hLip.uniformContinuous.comp_cauchySeq hu)
  have hyr : y ∈ range F := hemb.isClosed_range.mem_of_tendsto hy
    (Eventually.of_forall (fun k => mem_range_self (u k)))
  obtain ⟨x, rfl⟩ := hyr
  exact ⟨x, hemb.isEmbedding.isInducing.tendsto_nhds_iff.mpr hy⟩

end PoincareConjecture.RiemannianMetric
