import PoincareConjecture.Proofs.M34.Standard.GeneralizedCompactMetricComparison
import PoincareConjecture.Proofs.M34.Standard.GeneralizedReverseBall
import PoincareConjecture.Proofs.M34.Standard.QuadraticTangentComparison
import PoincareConjecture.Proofs.M34.Standard.ScaledTangentComparison

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
variable (C : GeneralizedBlowupConvergence S J)

private local instance : TopologicalSpace C.limit.carrier.carrier :=
  C.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.limit.carrier.carrier :=
  C.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ C.limit.carrier.carrier := C.limit.carrier.isManifold

theorem limitNoncollapse_compact_inner_zero
    {K : Set C.limit.sliceCarrier.carrier} (hK : IsCompact K) :
    let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
      fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
    ∀ᶠ k : ℕ in atTop, K ⊆ C.exhaustion.space k ∧
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        (1 / 2 : ℝ) * (C.limit.flow.metric 0).inner x v v ≤
          (C.embedding k).pullbackInner 0 (h0 k) x v v ∧
        (C.embedding k).pullbackInner 0 (h0 k) x v v ≤
          2 * (C.limit.flow.metric 0).inner x v v := by
  exact C.eventually_pullback_inner_comparison_zero hK

theorem limitNoncollapse_chart_inner_zero
    (q : C.limit.sliceCarrier.carrier)
    {H : Set (EuclideanSpace ℝ (Fin 3))} (hH : IsCompact H)
    (hHt : H ⊆ (extChartAt (𝓡 3) q).target) :
    let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
      fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
    ∀ᶠ k : ℕ in atTop,
      (extChartAt (𝓡 3) q).symm '' H ⊆ C.exhaustion.space k ∧
      ∀ y ∈ H, ∀ v : EuclideanSpace ℝ (Fin 3),
        let A := mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm y
        (1 / 2 : ℝ) * (C.limit.flow.metric 0).inner
            ((extChartAt (𝓡 3) q).symm y) (A v) (A v) ≤
          (C.embedding k).pullbackInner 0 (h0 k)
            ((extChartAt (𝓡 3) q).symm y) (A v) (A v) ∧
        (C.embedding k).pullbackInner 0 (h0 k)
            ((extChartAt (𝓡 3) q).symm y) (A v) (A v) ≤
          2 * (C.limit.flow.metric 0).inner
            ((extChartAt (𝓡 3) q).symm y) (A v) (A v) := by
  exact C.eventually_chart_pullback_inner_comparison_zero q hH hHt

theorem limitNoncollapse_forward_tangent_bound
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    {x : M} {y : N} (v : TangentSpace (𝓡 n) x)
    (w : TangentSpace (𝓡 m) y) {Q : ℝ} (hQ : 0 < Q)
    (hbound : Q * h.inner y w w ≤ 2 * g.inner x v v) :
    h.tangentNorm y w ≤ (2 / Real.sqrt Q) * g.tangentNorm x v := by
  exact RiemannianMetric.tangentNorm_le_two_div_sqrt_mul_of_scaled_inner_le
    g h v w hQ hbound

theorem limitNoncollapse_inverse_tangent_bound
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    {x : M} {y : N} (v : TangentSpace (𝓡 n) x)
    (w : TangentSpace (𝓡 m) y) {Q : ℝ} (hQ : 0 ≤ Q)
    (hbound : (1 / 2 : ℝ) * g.inner x v v ≤ Q * h.inner y w w) :
    g.tangentNorm x v ≤ 2 * Real.sqrt Q * h.tangentNorm y w := by
  exact RiemannianMetric.tangentNorm_le_two_sqrt_mul_of_half_inner_le
    g h v w hQ hbound

theorem limitNoncollapse_reverse_ball_zero
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U) (hU : IsOpen U)
    (h0 : 0 ∈ I) (hscale : 0 < scale) (g : RiemannianMetric 3 C.carrier)
    {o : C.carrier} (ho : o ∈ U) {p : F.point}
    (hp : e.pointMap 0 h0 o = p) {a : ℝ}
    (hcover : ∀ x ∈ (F.metric p.1).ball p.2 (a / Real.sqrt scale),
      ∃ y ∈ U, e.pointMap 0 h0 y = (⟨p.1, x⟩ : F.point))
    (hbound : ∀ x ∈ U, g.edist o x ≤ ENNReal.ofReal (2 * a) →
      ∀ v : TangentSpace (𝓡 3) x,
        (1 / 2 : ℝ) * g.inner x v v ≤ e.pullbackInner 0 h0 x v v) :
    ∀ x ∈ (F.metric p.1).ball p.2 (a / Real.sqrt scale),
      ∃ y ∈ g.ball o (2 * a) ∩ U,
        e.pointMap 0 h0 y = (⟨p.1, x⟩ : F.point) := by
  exact e.reverse_ball_zero_of_pullback_inner_lower hU h0 hscale g ho hp
    hcover hbound

end PoincareConjecture.M47
