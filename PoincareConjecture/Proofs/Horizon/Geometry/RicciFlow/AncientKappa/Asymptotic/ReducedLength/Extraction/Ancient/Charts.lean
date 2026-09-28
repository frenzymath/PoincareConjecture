import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.MetricBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.TimeGrowth


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

noncomputable def sourcePoint (G : AncientCompactTimeConvergence S) (k : ℕ)
    (x : G.limit.carrier.carrier) : M := ((G.embedding k).toFun (-1, x)).2

noncomputable def reducedLengthPullback (G : AncientCompactTimeConvergence S)
    (k : ℕ) (x : G.limit.carrier.carrier) (τ : ℝ) : ℝ :=
  reducedLength K.flow 0 S.reference (G.sourcePoint k x) (S.scale (G.subsequence k) * τ)

theorem sourcePoint_base (G : AncientCompactTimeConvergence S) (k : ℕ) :
    G.sourcePoint k G.limit.base = S.base (G.subsequence k) :=
  congrArg Prod.snd (G.base_preserving k)

theorem sourcePoint_eq_at (G : AncientCompactTimeConvergence S) (k : ℕ)
    {t : ℝ} (ht : t ∈ ancientM18TimeWindow k) {x : G.limit.carrier.carrier}
    (hx : x ∈ G.exhaustion k) : G.sourcePoint k x = ((G.embedding k).toFun (t, x)).2 :=
  G.spatial_time_independent k (-1) t x (G.time_window_base k) ht hx

noncomputable def sourceCoordinateChart (G : AncientCompactTimeConvergence S)
    (k : ℕ) (q : G.limit.carrier.carrier) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M := by
  classical
  exact if h : ancientM18TimeWindow k ∈ 𝓝 (-1 : ℝ) then
    (chartAt (EuclideanSpace ℝ (Fin n)) q).symm.trans
      ((G.embedding k).spatialHomeomorph (G.exhaustion_open k) h)
    else (chartAt (EuclideanSpace ℝ (Fin n)) S.reference).symm

theorem sourceCoordinateChart_apply (G : AncientCompactTimeConvergence S)
    (k : ℕ) (q : G.limit.carrier.carrier)
    (hk : ancientM18TimeWindow k ∈ 𝓝 (-1 : ℝ)) (x : EuclideanSpace ℝ (Fin n)) :
    G.sourceCoordinateChart k q x =
      G.sourcePoint k ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) := by
  simp only [sourceCoordinateChart, dif_pos hk]
  rfl

theorem sourceCoordinateChart_smooth (G : AncientCompactTimeConvergence S)
    (k : ℕ) (q : G.limit.carrier.carrier) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (G.sourceCoordinateChart k q)
        (G.sourceCoordinateChart k q).source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ (G.sourceCoordinateChart k q).symm
        (G.sourceCoordinateChart k q).target := by
  classical
  by_cases hk : ancientM18TimeWindow k ∈ 𝓝 (-1 : ℝ)
  · have hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞
        ((G.embedding k).spatialHomeomorph (G.exhaustion_open k) hk)
        ((G.embedding k).spatialHomeomorph (G.exhaustion_open k) hk).source :=
      fun x hx => ((G.embedding k).spatialMap_contMDiffAt_of_time_nhds
        (G.exhaustion_open k) hk hx).contMDiffWithinAt
    have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞
        ((G.embedding k).spatialHomeomorph (G.exhaustion_open k) hk).symm
        ((G.embedding k).spatialHomeomorph (G.exhaustion_open k) hk).target := by
      rintro _ ⟨x, hx, rfl⟩
      exact ((G.embedding k).spatialInverse_contMDiffAt (G.exhaustion_open k) hk hx).contMDiffWithinAt
    simp only [sourceCoordinateChart, dif_pos hk]
    exact ⟨hf.comp (contMDiffOn_chart_symm.mono inter_subset_left) inter_subset_right,
      contMDiffOn_chart.comp (hi.mono inter_subset_left) inter_subset_right⟩
  · simp only [sourceCoordinateChart, dif_neg hk]
    exact ⟨contMDiffOn_chart_symm, contMDiffOn_chart⟩

theorem eventually_subset_sourceCoordinateChart (G : AncientCompactTimeConvergence S)
    (q : G.limit.carrier.carrier) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCompact A) (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target) :
    ∀ᶠ k in atTop, A ⊆ (G.sourceCoordinateChart k q).source := by
  have hc : IsCompact ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm '' A) :=
    hA.image_of_continuousOn ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm.continuousOn.mono hchart)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hc
  filter_upwards [eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0),
    eventually_ge_atTop j] with k hk hjk x hx
  simp only [sourceCoordinateChart, dif_pos hk]
  exact ⟨hchart hx, G.exhaustion_monotone hjk (hj (mem_image_of_mem _ hx))⟩

theorem sourceCoordinateChart_tangentNorm_eq (G : AncientCompactTimeConvergence S)
    (k : ℕ) (q : G.limit.carrier.carrier)
    (hk : ancientM18TimeWindow k ∈ 𝓝 (-1 : ℝ))
    {t : ℝ} (ht : ancientM18TimeWindow k ∈ 𝓝 t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (G.sourceCoordinateChart k q).source)
    (v : EuclideanSpace ℝ (Fin n)) :
    ((S.rescaling (G.subsequence k)).flow.metric t).tangentNorm (G.sourceCoordinateChart k q x)
        (mfderiv (𝓡 n) (𝓡 n) (G.sourceCoordinateChart k q) x v) =
      Real.sqrt (ancientPullbackInnerValue (G.embedding k) t
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x v)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm x v)) := by
  let c := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  let ψ : G.limit.carrier.carrier → M := fun y => ((G.embedding k).toFun (t, y)).2
  have hx' : x ∈ c.source ∧ c x ∈ G.exhaustion k := by
    rw [sourceCoordinateChart, dif_pos hk] at hx
    exact hx
  have heq : (G.sourceCoordinateChart k q : _ → _) =ᶠ[𝓝 x] ψ ∘ c := by
    filter_upwards [(G.sourceCoordinateChart k q).open_source.mem_nhds hx] with y hy
    have hy' : y ∈ c.source ∧ c y ∈ G.exhaustion k := by
      rw [sourceCoordinateChart, dif_pos hk] at hy
      exact hy
    rw [G.sourceCoordinateChart_apply k q hk]
    exact G.sourcePoint_eq_at k (mem_of_mem_nhds ht) hy'.2
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c x :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_source.mem_nhds hx'.1)
  have hψ : ContMDiffAt (𝓡 n) (𝓡 n) ∞ ψ (c x) :=
    (G.embedding k).spatialMap_contMDiffAt_of_time_nhds (G.exhaustion_open k) ht hx'.2
  rw [RiemannianMetric.tangentNorm, heq.eq_of_nhds, heq.mfderiv_eq,
    mfderiv_comp x (hψ.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
  rfl

end PoincareConjecture.AncientCompactTimeConvergence
