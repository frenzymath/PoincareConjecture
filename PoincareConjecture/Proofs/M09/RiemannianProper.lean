import PoincareConjecture.Definitions.Ch04.Harnack
import PoincareConjecture.Proofs.M09.CompactRadial
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

theorem connected_edist_ne_top {X : Type*} [EMetricSpace X] [ConnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have hball : Metric.eball x ⊤ = Set.univ :=
    IsClopen.eq_univ ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
      ⟨x, Metric.mem_eball_self (by simp)⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hball]; trivial
  apply ne_of_lt
  simpa only [Metric.mem_eball, edist_comm] using hy

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [ConnectedSpace M]

@[reducible] noncomputable def selectedMetricSpace (g : RiemannianMetric n M) : MetricSpace M :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  EMetricSpace.toMetricSpace connected_edist_ne_top

theorem selectedMetricSpace_edist (g : RiemannianMetric n M) (x y : M) :
    letI : MetricSpace M := selectedMetricSpace g
    edist x y = g.edist x y := rfl

theorem selectedMetricSpace_complete (g : RiemannianMetric n M) (hcomplete : MetricComplete g) :
    letI : MetricSpace M := selectedMetricSpace g
    CompleteSpace M := hcomplete

theorem selectedMetricSpace_radial_projection (g : RiemannianMetric n M) :
    letI : MetricSpace M := selectedMetricSpace g
    ∀ (x : M) (R r ε : ℝ), 0 ≤ r → r ≤ R → 0 < ε →
      Metric.closedBall x R ⊆ Metric.thickening (R - r + ε) (Metric.closedBall x r) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : MetricSpace M := selectedMetricSpace g
  have hed (a b : M) : Manifold.riemannianEDist (𝓡 n) a b = ENNReal.ofReal (dist a b) :=
    edist_dist a b
  intro x R r ε hr hrR hε y hy
  have hδ : 0 < R - r + ε := by linarith
  by_cases hsmall : dist x y ≤ r
  · apply Metric.mem_thickening_iff.mpr
    refine ⟨y, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_comm] using hsmall
    · simpa only [dist_self] using hδ
  have hrxy : r < dist x y := lt_of_not_ge hsmall
  have hshort : Manifold.riemannianEDist (𝓡 n) x y <
      ENNReal.ofReal (dist x y + ε) := by
    rw [hed]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [dist_nonneg (x := x) (y := y)])).mpr
      (by linarith)
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt hshort
  have hcont : ContinuousOn (fun t ↦ dist x (γ t)) (Set.Icc 0 1) :=
    continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ.continuousOn)
  have hrange : r ∈ Set.Icc (dist x (γ 0)) (dist x (γ 1)) := by
    simpa only [Set.mem_Icc, hγ0, hγ1, dist_self] using And.intro hr hrxy.le
  obtain ⟨s, hs, hdist⟩ := intermediate_value_Icc zero_le_one hcont hrange
  change dist x (γ s) = r at hdist
  have hp := Manifold.riemannianEDist_le_pathELength
    (hγ.mono (Set.Icc_subset_Icc le_rfl hs.2)) hγ0 rfl hs.1
  have htail := Manifold.riemannianEDist_le_pathELength
    (hγ.mono (Set.Icc_subset_Icc hs.1 le_rfl)) rfl hγ1 hs.2
  rw [hed, hdist] at hp
  rw [hed] at htail
  have hsum : ENNReal.ofReal (r + dist (γ s) y) < ENNReal.ofReal (dist x y + ε) := by
    rw [ENNReal.ofReal_add hr dist_nonneg]
    exact (add_le_add hp htail).trans_lt
      ((Manifold.pathELength_add hs.1 hs.2).trans_lt hlength)
  have hsum' : r + dist (γ s) y < dist x y + ε :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith [dist_nonneg (x := x) (y := y)])).mp hsum
  apply Metric.mem_thickening_iff.mpr
  refine ⟨γ s, ?_, ?_⟩
  · change dist (γ s) x ≤ r
    rw [dist_comm, hdist]
  · have hy' : dist x y ≤ R := by simpa only [Metric.mem_closedBall, dist_comm] using hy
    rw [dist_comm]
    linarith

theorem selectedMetricSpace_proper (g : RiemannianMetric n M) (hcomplete : MetricComplete g) :
    letI : MetricSpace M := selectedMetricSpace g
    ProperSpace M := by
  letI : MetricSpace M := selectedMetricSpace g
  letI : CompleteSpace M := selectedMetricSpace_complete g hcomplete
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  exact properSpace_of_approximate_radial_projection (selectedMetricSpace_radial_projection g)

theorem isCompact_closure_metric_ball (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) (p : M) (r : ℝ) : IsCompact (closure (g.ball p r)) := by
  letI : MetricSpace M := selectedMetricSpace g
  letI : ProperSpace M := selectedMetricSpace_proper g hcomplete
  have hball : g.ball p r = Metric.ball p r := by
    have he : g.ball p r = Metric.eball p (ENNReal.ofReal r) := by
      ext y
      change g.edist p y < ENNReal.ofReal r ↔ edist y p < ENNReal.ofReal r
      rw [← selectedMetricSpace_edist g p y, edist_comm]
    exact he.trans Metric.eball_ofReal
  rw [hball]
  exact (isCompact_closedBall p r).of_isClosed_subset isClosed_closure
    Metric.closure_ball_subset_closedBall

end PoincareConjecture.Proofs.M09
