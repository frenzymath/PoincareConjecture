import PoincareConjecture.Proofs.M47.LimitFiniteEndpointMetric
import PoincareConjecture.Proofs.M47.LimitNoncollapseFiniteHarnackDomain
import PoincareConjecture.Proofs.M34.Standard.NonnegativeRicciMetric
import PoincareConjecture.Proofs.M35.RawFlow.Completeness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance finiteEndpointCompleteTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance finiteEndpointCompleteCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteEndpointCompleteManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
private local instance finiteEndpointCompleteT3 :
    T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space

local notation "U" => (fun m : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space m) (G.exhaustion.space_open m))

theorem limitFinite_original_metric_floor (h04 : RicciFlowCurvatureTheory.{u})
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H)
    (x : G.limit.sliceCarrier.carrier) (v : E) :
    (G.limit.flow.metric 0).inner x v v ≤ (G.limit.flow.metric t).inner x v v := by
  have hJ : Icc t 0 ⊆ blowupBackwardInterval H :=
    G.limit.flow.interval.out ht G.limit.zero_mem
  have hanti := G.limit.flow.inner_self_antitoneOn_of_nonnegative_ricci
    (convex_Icc t 0) hJ x v
    (fun s hs => (limitFinite_ricci_bounds h04 G.limit s (hJ hs) x v).1)
  exact hanti ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1

theorem limitFinite_endpoint_complete (h04 : RicciFlowCurvatureTheory.{u})
    (hfinite : H ≠ ⊤) (d : ℕ → ℝ) (hd : ∀ m, 0 < d m)
    (A : ∀ m, RicciFlow 3 (U m) (Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4)))
    (gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier)
    (hendpoint : ∀ m (x : U m) (v w : E),
      ((A m).metric (-H.toReal)).inner x v w =
        gE.inner x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w))
    (hold : ∀ m t, t ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4) →
      t ∈ blowupBackwardInterval H → ∀ (x : U m) (v w : E),
        ((A m).metric t).inner x v w =
          (G.limit.flow.metric t).inner x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w)) :
    (∀ (x : G.limit.sliceCarrier.carrier) (v : E),
      (G.limit.flow.metric 0).inner x v v ≤ gE.inner x v v) ∧ MetricComplete gE := by
  have hH : 0 < H := by simpa using G.limit.zero_mem.2
  have hT := limitFinite_horizon_pos hH hfinite
  have hquad (x : G.limit.sliceCarrier.carrier) (v : E) :
      (G.limit.flow.metric 0).inner x v v ≤ gE.inner x v v := by
    have hx : x ∈ ⋃ m, G.exhaustion.space m := by
      rw [G.exhaustion.space_covers]
      exact mem_univ x
    obtain ⟨m, hm⟩ := mem_iUnion.mp hx
    let y : U m := ⟨x, hm⟩
    have ht0 : -H.toReal ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4) :=
      ⟨by linarith [hd m], by linarith [hd m]⟩
    have hcont := ((A m).equation (-H.toReal) ht0 y v v).hasDerivAt
      (isOpen_Ioo.mem_nhds ht0)
    have hlim : Tendsto (fun t => ((A m).metric t).inner y v v) (𝓝[>] (-H.toReal))
        (𝓝 (((A m).metric (-H.toReal)).inner y v v)) :=
      hcont.continuousAt.mono_left nhdsWithin_le_nhds
    have hbound : ∀ᶠ t in 𝓝[>] (-H.toReal),
        (G.limit.flow.metric 0).inner x v v ≤ ((A m).metric t).inner y v v := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht0),
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (neg_lt_zero.mpr hT)),
        self_mem_nhdsWithin] with t htJ htneg htright
      have htold : t ∈ blowupBackwardInterval H := by
        rw [limitFinite_domain_eq hfinite]
        exact ⟨htright, htneg.le⟩
      have hread := hold m t htJ htold y v v
      simp only [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply]
        at hread
      rw [hread]
      exact limitFinite_original_metric_floor G h04 t htold x v
    have h := ge_of_tendsto hlim hbound
    have hread := hendpoint m y v v
    simp only [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply]
      at hread
    exact h.trans_eq hread
  refine ⟨hquad, RiemannianMetric.metricComplete_of_tangentNorm_le
    (G.limit.flow.metric 0) gE (G.limit.complete 0 G.limit.zero_mem)
    (C := 1) zero_lt_one ?_⟩
  intro x v
  change Real.sqrt ((G.limit.flow.metric 0).inner x v v) ≤
    1 * Real.sqrt (gE.inner x v v)
  simpa only [one_mul] using Real.sqrt_le_sqrt (hquad x v)

end PoincareConjecture.M47
