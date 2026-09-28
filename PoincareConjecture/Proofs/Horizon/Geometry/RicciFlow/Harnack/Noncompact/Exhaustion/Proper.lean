import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] {J : Set ℝ} {F : RicciFlow n M J} {O : M}

theorem SmoothExhaustion.isCompact_sublevel_component
    (S : SmoothExhaustion F O) {t : ℝ} (ht : t ∈ J)
    (hcomplete : MetricComplete (F.metric t)) (r : ℝ) :
    IsCompact {x | S.toFun x ≤ r ∧ (F.metric t).edist O x ≠ ⊤} := by
  let g := F.metric t
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hclosed : IsClosed {x | S.toFun x ≤ r ∧ g.edist O x ≠ ⊤} := by
    apply (isClosed_le S.smooth.continuous continuous_const).inter
    change IsClosed {x | g.edist O x ≠ ⊤}
    have heq : {x | g.edist O x ≠ ⊤} = Metric.eball O ⊤ := by
      ext x
      simp only [Metric.mem_eball, edist_comm x O, lt_top_iff_ne_top]
      rfl
    rw [heq]
    exact Metric.isClosed_eball_top
  apply (g.isCompact_closedBall_of_metricComplete hcomplete O r).of_isClosed_subset hclosed
  intro x hx
  change S.toFun x ≤ r ∧ g.edist O x ≠ ⊤ at hx
  change g.edist O x ≤ ENNReal.ofReal r
  have hbound : (g.edist O x).toReal ≤ r := by
    have hlow := S.distance_lower t ht x
    change (g.edist O x).toReal + 1 ≤ S.toFun x at hlow
    linarith [hx.1]
  rw [← ENNReal.ofReal_toReal hx.2]
  exact ENNReal.ofReal_le_ofReal hbound

theorem SmoothExhaustion.isCompact_sublevel_of_metricComplete [PreconnectedSpace M]
    (S : SmoothExhaustion F O) {t : ℝ} (ht : t ∈ J)
    (hcomplete : MetricComplete (F.metric t)) (r : ℝ) :
    IsCompact {x | S.toFun x ≤ r} := by
  have heq : {x | S.toFun x ≤ r ∧ (F.metric t).edist O x ≠ ⊤} =
      {x | S.toFun x ≤ r} := by
    ext x
    exact and_iff_left ((F.metric t).edist_ne_top O x)
  rw [← heq]
  exact S.isCompact_sublevel_component ht hcomplete r

theorem exists_proper_smoothExhaustion_of_curvature_bound
    [PreconnectedSpace M] [NoncompactSpace M]
    (F : RicciFlow n M J) (t₀ T k₀ : ℝ) (ht₀ : t₀ ∈ J)
    (hT : ∀ t ∈ J, |t - t₀| ≤ T)
    (hcomplete : ∀ t ∈ J, MetricComplete (F.metric t))
    (hk₀ : 0 ≤ k₀)
    (hRm : ∀ t ∈ J, ∀ x, (F.connection t).curvatureTensorNorm x ≤ k₀)
    (hRicDeriv : ∀ t ∈ J, ∀ x (u v w : TangentSpace (𝓡 n) x),
      |(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
        x ![u, v, w]| ≤ k₀ * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v * (F.metric t).tangentNorm x w) :
    ∃ C : ℝ, 0 < C ∧ ∀ O : M, ∃ S : SmoothExhaustion F O,
      S.bound = C ∧ ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r} := by
  obtain ⟨C, hC, hS⟩ := F.exists_smoothExhaustion_of_curvature_bound t₀ T k₀
    ht₀ hT hcomplete hk₀ hRm hRicDeriv
  refine ⟨C, hC, ?_⟩
  intro O
  obtain ⟨S, hSb⟩ := hS O
  obtain ⟨t, ht⟩ := F.nontrivial.nonempty
  refine ⟨S, hSb, ?_⟩
  intro r
  exact S.isCompact_sublevel_of_metricComplete ht (hcomplete t ht) r

end PoincareConjecture.RicciFlow
