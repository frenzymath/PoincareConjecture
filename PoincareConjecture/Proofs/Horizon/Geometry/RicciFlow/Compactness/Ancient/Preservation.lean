import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Restriction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.CurvatureLimit











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {J : ℕ → Set ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (J k)) {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hT : 0 < T)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)

include hT htime



theorem curvatureTensorNorm_le_of_uniform_ball_bound {K : ℝ}
    (hbound : ∀ a b : ℝ, b < T → ∀ R : ℝ, 0 < R → ∀ᶠ k in atTop,
      ∀ t ∈ Ioo a b, ∀ x ∈ ((F k).metric t).ball (p k) R,
        ((F k).connection t).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ Iio T, ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).curvatureTensorNorm x ≤ K := by
  intro t ht x
  obtain ⟨a, b, ha, hb, hbT, htw⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr ht)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually (htime a b hbT))
  let W := G.window F (ha.trans hb) hbT.le N hN
  apply W.curvatureTensorNorm_le_of_uniform_ball_bound ⟨ha, hb⟩ ?_ t
    (htw (mem_singleton t)) x
  intro R hR
  exact (G.subsequence_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat N)).eventually
    (hbound a b hbT R hR)



theorem nonnegativeCurvatureOperator_of_eventually
    (hoperator : ∀ t ∈ Iio T, ∀ᶠ k in atTop, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Iio T, ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).NonnegativeCurvatureOperator x := by
  intro t ht
  obtain ⟨a, b, ha, hb, hbT, htw⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr ht)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually (htime a b hbT))
  let W := G.window F (ha.trans hb) hbT.le N hN
  apply W.nonnegativeCurvatureOperator_of_eventually t (htw (mem_singleton t))
  exact (G.subsequence_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat N)).eventually
    (hoperator t ht)



theorem scalar_lower_bound_le_mul_base_curvatureTensorNorm {c : ℝ}
    (hscalar : ∀ᶠ k in atTop, c ≤ ((F k).connection 0).scalarCurvature (p k)) :
    c ≤ (n : ℝ) ^ 2 * (G.limitFlow.connection 0).curvatureTensorNorm G.base := by
  obtain ⟨a, b, ha, hb, hbT, _⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr hT)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually (htime a b hbT))
  let W := G.window F (ha.trans hb) hbT.le N hN
  apply W.scalar_lower_bound_le_mul_base_curvatureTensorNorm ⟨ha, hb⟩
  exact (G.subsequence_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat N)).eventually
    hscalar

end PoincareConjecture.AncientPointedGeometricConvergence
