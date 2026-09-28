import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.TimeIndependent
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

private theorem exhaustion_mono_of_le
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) {j k : ℕ} (hjk : j ≤ k) :
    G.exhaustion j ⊆ G.exhaustion k := by
  induction k, hjk using Nat.le_induction with
  | base => exact Subset.rfl
  | succ k hk ih => exact ih.trans (G.exhaustion_increasing k)







theorem pullback_tangentNorm_le_sqrt_two
    {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}
    (G : PointedGeometricConvergence S) (j k : ℕ)
    {s : ℝ} (hs : s ∈ Ioo T' T)
    {x : G.limitCarrier.carrier}
    (v : G.limitCarrier.tangent x)
    (hclose : ∀ u w : G.limitCarrier.tangent x,
      G.limitCarrier.metricNorm (G.limitFlow.metricAt s) x u ≤ 1 →
      G.limitCarrier.metricNorm (G.limitFlow.metricAt s) x w ≤ 1 →
      |pullbackInnerValue G.limitFlow (S.flow (G.subsequence k))
          (G.embedding k) s x u w -
        G.limitCarrier.metricInner (G.limitFlow.metricAt s) x u w| < 1)
    : pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)
          s x v v ≤
        2 * G.limitCarrier.metricInner (G.limitFlow.metricAt s) x v v := by
  letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let C := S.carrier (G.subsequence k)
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let q := pullbackInnerValue G.limitFlow (S.flow (G.subsequence k))
    (G.embedding k) s x
  let g := G.limitCarrier.metricInner (G.limitFlow.metricAt s) x
  let a := G.limitCarrier.metricNorm (G.limitFlow.metricAt s) x v
  by_cases hv : v = 0
  · subst v
    simp [q, g, a, pullbackInnerValue, FlowCarrier.metricNorm,
      FlowCarrier.metricInner, RiemannianMetric.tangentNorm]
  have ha : 0 < a := by
    dsimp [a, FlowCarrier.metricNorm, FlowCarrier.metricInner]
    exact Real.sqrt_pos.2 ((G.limitFlow.metricAt s).pos x v hv)
  let u : G.limitCarrier.tangent x := a⁻¹ • v
  have hu : G.limitCarrier.metricNorm (G.limitFlow.metricAt s) x u = 1 := by
    dsimp [u, FlowCarrier.metricNorm, FlowCarrier.metricInner]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have ha2 : a ^ 2 = ((G.limitFlow.metricAt s).inner x) v v :=
      Real.sq_sqrt (le_of_lt ((G.limitFlow.metricAt s).pos x v hv))
    have hainv : a⁻¹ ^ 2 * a ^ 2 = 1 := by
      field_simp
    rw [show a⁻¹ * (a⁻¹ * ((G.limitFlow.metricAt s).inner x) v v) =
      a⁻¹ ^ 2 * a ^ 2 by rw [ha2]; ring]
    rw [hainv, Real.sqrt_one]
  have hc := hclose u u hu.le hu.le
  have hq : q u u ≤ g u u + 1 := by
    have := (le_abs_self (q u u - g u u)).trans_lt hc
    linarith
  have hqv : q v v ≤ 2 * g v v := by
    simp only [u, q, g, pullbackInnerValue, FlowCarrier.metricInner,
      map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at hq
    dsimp [a, FlowCarrier.metricNorm, FlowCarrier.metricInner] at hu
    dsimp [g, FlowCarrier.metricInner]
    dsimp [q, pullbackInnerValue]
    have ha2 : a ^ 2 = ((G.limitFlow.metricAt s).inner x) v v := Real.sq_sqrt
      (le_of_lt ((G.limitFlow.metricAt s).pos x v hv))
    have hainv : a⁻¹ ^ 2 * a ^ 2 = 1 := by field_simp
    nlinarith [ha2, hainv]
  exact hqv

end PoincareConjecture.PointedGeometricConvergence

namespace PoincareConjecture

variable {n : ℕ} {T' T : ℝ} {L C : FlowCarrier n}




theorem SmoothSpacetimeEmbedding.pathELength_le_sqrt_two
    {F : BasedFlow n T' T L} {G : BasedFlow n T' T C}
    {domain : Set (ℝ × L.carrier)}
    (e : SmoothSpacetimeEmbedding F G domain)
    {s : ℝ} {γ : ℝ → L.carrier}
    (hbound :
      letI : TopologicalSpace L.carrier := L.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier := L.chartedSpace
      letI : IsManifold (𝓡 n) ∞ L.carrier := L.isManifold
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ u ∈ Icc (0 : ℝ) 1,
        C.metricNorm (G.flow.metric s) ((e.toFun (s, γ u)).2)
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n)
              (fun z ↦ (e.toFun (s, γ z)).2) u 1) ≤
          Real.sqrt 2 * L.metricNorm (F.flow.metric s) (γ u)
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ u 1)) :
    letI : TopologicalSpace L.carrier := L.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier := L.chartedSpace
    letI : IsManifold (𝓡 n) ∞ L.carrier := L.isManifold
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    (G.flow.metric s).pathELength (fun z ↦ (e.toFun (s, γ z)).2) 0 1 ≤
      ENNReal.ofReal (Real.sqrt 2) * (F.flow.metric s).pathELength γ 0 1 := by
  letI : TopologicalSpace L.carrier := L.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier := L.chartedSpace
  letI : IsManifold (𝓡 n) ∞ L.carrier := L.isManifold
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  rw [RiemannianMetric.pathELength_eq_lintegral_tangentNorm,
    RiemannianMetric.pathELength_eq_lintegral_tangentNorm]
  calc
    (∫⁻ u in Icc (0 : ℝ) 1,
        ENNReal.ofReal
          ((G.flow.metric s).tangentNorm (e.toFun (s, γ u)).2
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n)
              (fun z ↦ (e.toFun (s, γ z)).2) u 1))) ≤
      ∫⁻ u in Icc (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt 2 *
          (F.flow.metric s).tangentNorm (γ u)
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ u 1)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact ENNReal.ofReal_le_ofReal (hbound u hu)
    _ = ∫⁻ u in Icc (0 : ℝ) 1,
        ENNReal.ofReal (Real.sqrt 2) *
          ENNReal.ofReal ((F.flow.metric s).tangentNorm (γ u)
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ u 1)) := by
      congr 1
      funext u
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.sqrt 2)]
    _ = ENNReal.ofReal (Real.sqrt 2) *
        ∫⁻ u in Icc (0 : ℝ) 1,
          ENNReal.ofReal ((F.flow.metric s).tangentNorm (γ u)
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ u 1)) := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top

end PoincareConjecture
