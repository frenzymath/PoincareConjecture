import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.CoordinatePullback
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LinearPostcompose










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SmoothSpacetimeEmbedding



theorem pullback_metric_CInfinity_of_spatial_jets
    {n : ℕ} {T' T : ℝ} {C : FlowCarrier n} {D : ℕ → FlowCarrier n}
    (F : BasedFlow n T' T C) (G : ∀ k, BasedFlow n T' T (D k))
    (E : ℕ → Set C.carrier)
    (hE : ∀ k, @IsOpen C.carrier C.topologicalSpace (E k)) (hEmono : Monotone E)
    (f : ∀ k, C.carrier → (D k).carrier)
    (hemb : ∀ k, letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : TopologicalSpace (D k).carrier := (D k).topologicalSpace
      Topology.IsOpenEmbedding (fun x : E k => f k x))
    (hf : ∀ k, letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : TopologicalSpace (D k).carrier := (D k).topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier := (D k).chartedSpace
      IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (f k) (E k))
    (hjets :
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      letI : ∀ k, TopologicalSpace (D k).carrier := fun k => (D k).topologicalSpace
      letI : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier :=
        fun k => (D k).chartedSpace
      letI : ∀ k, IsManifold (𝓡 n) ∞ (D k).carrier := fun k => (D k).isManifold
      ∀ (q : C.carrier) (r : ℕ) (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
        IsCompact K → K ⊆ Ioo T' T ×ˢ (extChartAt (𝓡 n) q).target →
        TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ r
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              ((G k).flow.metric z.1).pullbackCoefficients
                (f k ∘ (extChartAt (𝓡 n) q).symm) z.2))
          (iteratedFDeriv ℝ r
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              (F.flow.metric z.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm z.2))
          atTop K) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    ∀ (q : C.carrier) (j r : ℕ) (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
      IsCompact K →
      K ⊆ {p | p.1 ∈ Ioo T' T ∧ p.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm p.2 ∈ E j} →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N,
        ∀ a b : Fin n, ∀ p ∈ K,
          ‖MetricJet r
              (C.coordinateCoefficient q
                (pullbackInnerValue F (G k)
                  (of_spatial F (G k) (hE k) (f k) (hemb k) (hf k) (Ioo T' T))) a b) K p -
            MetricJet r
              (C.coordinateCoefficient q
                (fun t x v w => C.metricInner (F.metricAt t) x v w) a b) K p‖ < ε := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : ∀ k, TopologicalSpace (D k).carrier := fun k => (D k).topologicalSpace
  let : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (D k).carrier :=
    fun k => (D k).chartedSpace
  let : ∀ k, IsManifold (𝓡 n) ∞ (D k).carrier := fun k => (D k).isManifold
  intro q j r K hK hKU ε hε
  let c := extChartAt (𝓡 n) q
  let W := Ioo T' T ×ˢ (c.target ∩ c.symm ⁻¹' E j)
  have hW : IsOpen W := isOpen_Ioo.prod
    ((contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) (hE j))
  have hc (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx).contMDiffAt
      (extChartAt_target_mem_nhds' hx)
  have hlim : ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        (F.flow.metric z.1).pullbackCoefficients c.symm z.2) W := by
    intro z hz
    exact (F.flow.smooth.contDiffAt_spacetime_pullbackCoefficients
      isOpen_Ioo (hc z.2 hz.2.1) hz.1).contDiffWithinAt
  have hlocal : ∀ z ∈ W, ∃ V, IsOpen V ∧ z ∈ V ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((G k).flow.metric p.1).pullbackCoefficients (f k ∘ c.symm) p.2) V := by
    intro z hz
    refine ⟨W, hW, hz, ?_⟩
    filter_upwards [eventually_ge_atTop j] with k hjk p hp
    exact ((G k).flow.smooth.contDiffAt_spacetime_pullbackCoefficients isOpen_Ioo
      (((hf k) ⟨c.symm p.2, hEmono hjk hp.2.2⟩).contMDiffAt.comp p.2
        (hc p.2 hp.2.1)) hp.1).contDiffWithinAt
  have hscalar (a b : Fin n) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r
        (C.coordinateCoefficient q
          (pullbackInnerValue F (G k)
            (of_spatial F (G k) (hE k) (f k) (hemb k) (hf k) (Ioo T' T))) a b))
      (iteratedFDeriv ℝ r
        (C.coordinateCoefficient q
          (fun t x v w => C.metricInner (F.metricAt t) x v w) a b)) atTop K := by
    let L : (EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ b)).comp
        (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          (EuclideanSpace.basisFun (Fin n) ℝ a))
    have h := (Poincare.Analysis.Calculus.smooth_convergence_continuousLinearMap_comp
      L hW hlim hlocal (fun m A hA hAW =>
        hjets q m A hA (fun z hz => ⟨(hAW hz).1, (hAW hz).2.1⟩))).2 r K hK hKU
    apply (h.congr ?_).congr_right ?_
    · filter_upwards [eventually_ge_atTop j] with k hjk p hp
      exact (iteratedFDeriv_coordinateCoefficient_of_spatial F (G k)
        (hE k) (f k) (hemb k) (hf k) (Ioo T' T) q a b r p
        ⟨(hKU hp).2.1, hEmono hjk (hKU hp).2.2⟩).symm
    · intro p hp
      rfl
  have hεall : ∀ᶠ k in atTop, ∀ a b : Fin n, ∀ p ∈ K,
      ‖MetricJet r
          (C.coordinateCoefficient q
            (pullbackInnerValue F (G k)
              (of_spatial F (G k) (hE k) (f k) (hemb k) (hf k) (Ioo T' T))) a b) K p -
        MetricJet r
          (C.coordinateCoefficient q
            (fun t x v w => C.metricInner (F.metricAt t) x v w) a b) K p‖ < ε := by
    apply eventually_all.mpr
    intro a
    apply eventually_all.mpr
    intro b
    simpa only [MetricJet, dist_eq_norm, norm_sub_rev] using
      Metric.tendstoUniformlyOn_iff.mp (hscalar a b) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hεall
  exact ⟨max j N, le_max_left _ _, fun k hk => hN k ((le_max_right j N).trans hk)⟩

end PoincareConjecture.SmoothSpacetimeEmbedding
