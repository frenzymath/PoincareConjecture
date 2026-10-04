import PoincareLib.Geometry.Riemannian.Soul.Point.Terminal.PositiveRank

/-!
# Maximal contained normal disks

The admissible objects are actual normalized local exponential charts and
linear disks contained in the given set. Maximizing their finite-dimensional
rank ranges over every center, chart, and positive radius. Empty ambient
interior gives strict codimension, while two distinct points force positive
maximal rank.

Adapted from AxelWorkspace revision
`f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e`,
`MorganTianLib/Ch02/SoulGeometry/TerminalSet/LocalGeometry/MaximalDisk.lean`
and `SoulGeometry/LocalGeometry/RankGrowth.lean`.
Reference: Morgan--Tian, Theorem 2.7, p. 25.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- A linear disk contained in a set, expressed in an actual smooth normal
chart with its normalized derivative and radial geodesic equations. -/
structure ContainedNormalDisk (g : RiemannianMetric n M) (S : Set M) where
  center : M
  center_mem : center ∈ S
  radius : ℝ
  radius_pos : 0 < radius
  chart : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M
  source_eq : chart.source = Metric.ball 0 radius
  map_zero : chart 0 = center
  smooth : ContMDiffOn (𝓡 n) (𝓡 n) ∞ chart chart.source
  smooth_symm : ContMDiffOn (𝓡 n) (𝓡 n) ∞ chart.symm chart.target
  derivative_zero : HasFDerivAt (fun v => extChartAt (𝓡 n) center (chart v))
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0
  radial_geodesic : ∀ v ∈ Metric.ball 0 radius,
    g.IsGeodesicOn (fun t : ℝ => chart (t • v))
      {t : ℝ | t • v ∈ Metric.ball 0 radius}
  plane : Submodule ℝ (EuclideanSpace ℝ (Fin n))
  contained : chart '' (Metric.ball 0 radius ∩ (plane : Set (EuclideanSpace ℝ (Fin n)))) ⊆ S

namespace ContainedNormalDisk

variable {g : RiemannianMetric n M} {S : Set M}

noncomputable def rank (D : ContainedNormalDisk g S) : ℕ := Module.finrank ℝ D.plane

omit [T3Space M] in
theorem rank_le (D : ContainedNormalDisk g S) : D.rank ≤ n := by
  simpa [rank] using Submodule.finrank_le D.plane

omit [T3Space M] in
theorem rank_lt_of_empty_interior (D : ContainedNormalDisk g S)
    (hinterior : interior S = ∅) : D.rank < n :=
  finrank_lt_of_normal_disk_subset_empty_interior hinterior D.chart D.radius_pos
    (D.source_eq ▸ Subset.rfl) D.plane D.contained

omit [T3Space M] in
/-- Every point of the set in this normal chart contracts radially to the
disk's center while remaining in the set. -/
theorem radial_contraction (D : ContainedNormalDisk g S)
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 D.radius)
    (hend : D.chart v ∈ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    D.chart (t • v) ∈ S := by
  have hscaled {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
      u • v ∈ Metric.ball 0 D.radius := by
    rw [Metric.mem_ball, dist_zero_right] at hv ⊢
    rw [norm_smul, Real.norm_of_nonneg hu.1]
    exact (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg v)).trans_lt
      (by simpa only [one_mul] using hv)
  exact hconv (fun u : ℝ => D.chart (u • v)) 0 1
    (fun u hu => D.radial_geodesic v hv u (hscaled hu))
    (by simpa only [zero_smul, D.map_zero] using D.center_mem)
    (by simpa only [one_smul] using hend) ht

end ContainedNormalDisk

/-- The zero tangent subspace supplies a contained normal disk at each point
of the set, using a constructed local exponential chart. -/
theorem exists_zero_containedNormalDisk (g : RiemannianMetric n M) {S : Set M}
    {q : M} (hq : q ∈ S) :
    ∃ D : ContainedNormalDisk g S, D.center = q ∧ D.rank = 0 := by
  obtain ⟨r, e, hr, hsource, he0, he, hei, hed, hgeo⟩ := g.exists_radial_normal_chart q
  have hsub : e '' (Metric.ball 0 r ∩
      ((⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)))) ⊆ S := by
    rintro z ⟨v, ⟨_, hv⟩, rfl⟩
    have hv0 : v = 0 := hv
    simpa only [hv0, he0] using hq
  refine ⟨⟨q, hq, r, hr, e, hsource, he0, he, hei, hed, hgeo, ⊥, hsub⟩, rfl, ?_⟩
  simp [ContainedNormalDisk.rank]

/-- Finite ambient dimension supplies a disk of maximal rank among all
contained normal disks, with no regularity assumption on the set. -/
theorem exists_maximal_containedNormalDisk (g : RiemannianMetric n M) {S : Set M}
    (hne : S.Nonempty) :
    ∃ D : ContainedNormalDisk g S, ∀ D' : ContainedNormalDisk g S, D'.rank ≤ D.rank := by
  classical
  obtain ⟨q, hq⟩ := hne
  obtain ⟨D₀, _, _⟩ := g.exists_zero_containedNormalDisk hq
  let P : ℕ → Prop := fun k => ∃ D : ContainedNormalDisk g S, D.rank = k
  have hmax : P (Nat.findGreatest P n) :=
    Nat.findGreatest_spec D₀.rank_le ⟨D₀, rfl⟩
  obtain ⟨D, hD⟩ := hmax
  refine ⟨D, fun D' => ?_⟩
  have hle := Nat.le_findGreatest D'.rank_le (show P D'.rank from ⟨D', rfl⟩)
  simpa only [← hD] using hle

/-- Two distinct points in a totally convex set construct a contained normal
disk of rank one, without a supplied exponential disk. -/
theorem exists_rank_one_containedNormalDisk [ConnectedSpace M]
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g) {S : Set M}
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S)
    {x y : M} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ D : ContainedNormalDisk g S, D.rank = 1 := by
  obtain ⟨q, hq, r, e, V, hr, hsource, he0, he, hei, hed, hgeo, hdim, hsub⟩ :=
    g.exists_positive_normal_line_disk_of_two_points hcomplete hconv hx hy hxy
  exact ⟨⟨q, hq, r, hr, e, hsource, he0, he, hei, hed, hgeo, V, hsub⟩, hdim⟩

/-- A nontrivial totally convex set of empty ambient interior has a maximal
contained normal disk of positive rank and strict ambient codimension. -/
theorem exists_positive_maximal_containedNormalDisk [ConnectedSpace M]
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g) {S : Set M}
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S)
    (hinterior : interior S = ∅)
    {x y : M} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    ∃ D : ContainedNormalDisk g S, 0 < D.rank ∧ D.rank < n ∧
      ∀ D' : ContainedNormalDisk g S, D'.rank ≤ D.rank := by
  obtain ⟨D, hmax⟩ := g.exists_maximal_containedNormalDisk ⟨x, hx⟩
  obtain ⟨D₁, hD₁⟩ := g.exists_rank_one_containedNormalDisk hcomplete hconv hx hy hxy
  have hpos : 0 < D.rank := by
    have hle := hmax D₁
    rw [hD₁] at hle
    exact hle
  exact ⟨D, hpos, D.rank_lt_of_empty_interior hinterior, hmax⟩

end PoincareMT.RiemannianMetric
