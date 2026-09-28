import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.MinimizingSegments
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

theorem exists_nearest_frontier (g : RiemannianMetric n M)
    {D : Set M} (hD : IsCompact D) (hfront : (frontier D).Nonempty)
    {x : M} (hx : x ∈ interior D) :
    ∃ y ∈ frontier D, 0 < (g.edist x y).toReal ∧
      ∀ z ∈ frontier D, (g.edist x y).toReal ≤ (g.edist x z).toReal := by
  have hcompact : IsCompact (frontier D) :=
    hD.of_isClosed_subset isClosed_frontier hD.isClosed.frontier_subset
  obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn hfront
    (g.continuous_toReal_edist x).continuousOn
  refine ⟨y, hy, ?_, hmin⟩
  have hxy : x ≠ y := by
    intro heq
    exact hy.2 (heq ▸ hx)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  exact ENNReal.toReal_pos (ne_of_gt (edist_pos.mpr hxy)) (g.edist_ne_top x y)

theorem ball_subset_interior_of_le_frontier_distance
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {D : Set M} {x : M} (hx : x ∈ interior D) {r : ℝ}
    (hfront : ∀ z ∈ frontier D, r ≤ (g.edist x z).toReal) :
    g.ball x r ⊆ interior D := by
  intro q hq
  have hqr : (g.edist x q).toReal < r := ENNReal.toReal_lt_of_lt_ofReal hq
  obtain ⟨ε, hε, γ, hgeo, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc x q
  have hI : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image γ (hgeo.contMDiffOn.continuousOn.mono hI)
  have hdisjoint : Disjoint (γ '' Icc (0 : ℝ) 1) (frontier D) := by
    apply disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ hz
    have hdist := hmin 0 (by simp) t ht
    rw [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1] at hdist
    have hdist_real : (g.edist x (γ t)).toReal = t * (g.edist x q).toReal := by
      rw [hdist, ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.1]
    have hle : (g.edist x (γ t)).toReal ≤ (g.edist x q).toReal := by
      rw [hdist_real]
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg ht.2
    exact (not_le_of_gt (hle.trans_lt hqr)) (hfront (γ t) hz)
  have hsubset := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    hconn hdisjoint ⟨x, ⟨0, by simp, hγ0⟩, hx⟩
  apply hsubset
  exact ⟨1, by simp, hγ1⟩

theorem frontier_distance_le_of_not_mem_interior
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {D : Set M} {x : M} (hx : x ∈ interior D) {r : ℝ}
    (hfront : ∀ z ∈ frontier D, r ≤ (g.edist x z).toReal)
    {q : M} (hq : q ∉ interior D) : r ≤ (g.edist x q).toReal := by
  by_contra h
  have hball : q ∈ g.ball x r :=
    (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top x q)).mpr (lt_of_not_ge h)
  exact hq (g.ball_subset_interior_of_le_frontier_distance hc hx hfront hball)

theorem exists_unit_speed_minimizing_geodesic_to_frontier
    (g : RiemannianMetric n M) (hc : MetricComplete g)
    {D : Set M} (hD : IsCompact D) (hfront : (frontier D).Nonempty)
    {x : M} (hx : x ∈ interior D) :
    ∃ y ∈ frontier D, 0 < (g.edist x y).toReal ∧
      (∀ z ∈ frontier D, (g.edist x y).toReal ≤ (g.edist x z).toReal) ∧
      ∃ γ : ℝ → M, γ 0 = x ∧ γ (g.edist x y).toReal = y ∧
        g.IsGeodesicOn γ (Icc (0 : ℝ) (g.edist x y).toReal) ∧
        (∀ t ∈ Icc (0 : ℝ) (g.edist x y).toReal,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) ∧
        (∀ s ∈ Icc (0 : ℝ) (g.edist x y).toReal,
          ∀ t ∈ Icc (0 : ℝ) (g.edist x y).toReal,
            g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) ∧
        MapsTo γ (Ico (0 : ℝ) (g.edist x y).toReal) (interior D) := by
  obtain ⟨y, hy, hL, hnearest⟩ := g.exists_nearest_frontier hD hfront hx
  obtain ⟨γ, hγ0, hγL, hgeo, hspeed, hmin⟩ :=
    g.exists_unit_speed_minimizing_geodesic_of_metricComplete hc x y hL
  refine ⟨y, hy, hL, hnearest, γ, hγ0, hγL, hgeo, hspeed, hmin, ?_⟩
  have hconn : IsPreconnected (γ '' Ico (0 : ℝ) (g.edist x y).toReal) :=
    isPreconnected_Ico.image γ
      (hgeo.contMDiffOn.continuousOn.mono Ico_subset_Icc_self)
  have hdisjoint : Disjoint (γ '' Ico (0 : ℝ) (g.edist x y).toReal)
      (frontier D) := by
    apply disjoint_left.mpr
    rintro z ⟨t, ht, rfl⟩ hz
    have hdist := hmin 0 ⟨le_rfl, hL.le⟩ t ⟨ht.1, ht.2.le⟩
    rw [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1] at hdist
    have hdist_real : (g.edist x (γ t)).toReal = t := by
      rw [hdist, ENNReal.toReal_ofReal ht.1]
    exact (not_le_of_gt ht.2) (hdist_real ▸ hnearest (γ t) hz)
  have hsubset := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    hconn hdisjoint ⟨x, ⟨0, ⟨le_rfl, hL⟩, hγ0⟩, hx⟩
  intro t ht
  exact hsubset ⟨t, ht, rfl⟩

end PoincareConjecture.RiemannianMetric
