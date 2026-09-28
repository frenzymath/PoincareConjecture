import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.UnitInterval











noncomputable section
open Set Metric Filter Topology

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple.ChartChain

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]


structure ChartBall (I : ModelWithCorners ℝ E H) (U : Set M) where
  center : M
  radius : ℝ
  radius_pos : 0 < radius
  in_target : closedBall (extChartAt I center center) radius ⊆
    (extChartAt I center).target
  in_domain : (extChartAt I center).symm ''
    closedBall (extChartAt I center center) radius ⊆ U

namespace ChartBall

variable {U : Set M} (B : ChartBall I U)


def domain : Set M := (extChartAt I B.center).symm ''
  closedBall (extChartAt I B.center B.center) B.radius


def core : Set M := (extChartAt I B.center).source ∩
  extChartAt I B.center ⁻¹' ball (extChartAt I B.center B.center) B.radius


theorem isCompact_domain [FiniteDimensional ℝ E] : IsCompact B.domain :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((continuousOn_extChartAt_symm B.center).mono B.in_target)


theorem domain_subset : B.domain ⊆ U := B.in_domain


theorem domain_chart : B.domain ⊆ (chartAt H B.center).source := by
  rintro x ⟨y, hy, rfl⟩
  simpa only [extChartAt_source] using
    (extChartAt I B.center).map_target (B.in_target hy)


theorem isOpen_core : IsOpen B.core :=
  isOpen_extChartAt_preimage' B.center isOpen_ball


theorem center_mem_core : B.center ∈ B.core :=
  ⟨mem_extChartAt_source B.center, mem_ball_self B.radius_pos⟩


theorem core_subset_interior : B.core ⊆ interior B.domain := by
  apply interior_maximal _ B.isOpen_core
  intro x hx
  exact ⟨extChartAt I B.center x, ball_subset_closedBall hx.2,
    (extChartAt I B.center).left_inv hx.1⟩


theorem inverse_mem_core {y : E}
    (hy : y ∈ ball (extChartAt I B.center B.center) B.radius) :
    (extChartAt I B.center).symm y ∈ B.core := by
  have ht := B.in_target (ball_subset_closedBall hy)
  exact ⟨(extChartAt I B.center).map_target ht,
    by simpa only [mem_preimage, (extChartAt I B.center).right_inv ht] using hy⟩

end ChartBall


theorem exists_chartBall [I.Boundaryless] {U : Set M} (hU : IsOpen U)
    {p : M} (hp : p ∈ U) :
    ∃ B : ChartBall I U, B.center = p := by
  have ht := (extChartAt I p).map_source (mem_extChartAt_source p)
  have hc : ContinuousAt (extChartAt I p).symm (extChartAt I p p) :=
    ((continuousOn_extChartAt_symm p) _ ht).continuousAt
      ((isOpen_extChartAt_target p).mem_nhds ht)
  have hU' : (extChartAt I p).symm ⁻¹' U ∈ 𝓝 (extChartAt I p p) :=
    hc.preimage_mem_nhds (hU.mem_nhds (by
      simpa only [(extChartAt I p).left_inv (mem_extChartAt_source p)] using hp))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((isOpen_extChartAt_target p).mem_nhds ht) hU')
  have hclosed := (closedBall_subset_ball (half_lt_self hr)).trans hball
  exact ⟨⟨p, r / 2, half_pos hr, fun _ hy => (hclosed hy).1,
    by rintro _ ⟨y, hy, rfl⟩; exact (hclosed hy).2⟩, rfl⟩

include I in

theorem manifold_locallyPathConnected : LocallyPathConnectedSpace M := by
  let : LocallyPathConnectedSpace (range I) := I.convex_range.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace H :=
    I.isClosedEmbedding.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H M

include I in

theorem exists_compact_path {U : Set M} (hU : IsOpen U) (hconn : IsConnected U)
    {p q : M} (hp : p ∈ U) (hq : q ∈ U) :
    ∃ γ : Path p q, IsCompact (range γ) ∧ range γ ⊆ U := by
  let : LocallyPathConnectedSpace M := manifold_locallyPathConnected (I := I)
  have hj := (hU.isConnected_iff_isPathConnected.mp hconn).joinedIn p hp q hq
  exact ⟨hj.somePath, isCompact_range hj.somePath.continuous,
    by rintro _ ⟨t, rfl⟩; exact hj.somePath_mem t⟩


structure Subdivision {U : Set M} {p q : M} (γ : Path p q) where
  count : ℕ
  count_pos : 0 < count
  cut : ℕ → unitInterval
  cut_zero : cut 0 = 0
  cut_last : cut count = 1
  monotone_cut : Monotone cut
  ball : Fin count → ChartBall I U
  subordinate : ∀ i : Fin count, ∀ t ∈ Icc (cut i) (cut (i + 1)),
    γ t ∈ (ball i).core


theorem exists_subdivision [I.Boundaryless] {U : Set M} (hU : IsOpen U) {p q : M}
    (γ : Path p q) (hγ : range γ ⊆ U) : Nonempty (Subdivision (I := I) (U := U) γ) := by
  classical
  have hc : ∀ t : unitInterval, ∃ B : ChartBall I U, γ t ∈ B.core := by
    intro t
    obtain ⟨B, hB⟩ := exists_chartBall (I := I) hU (hγ (mem_range_self t))
    exact ⟨B, hB ▸ B.center_mem_core⟩
  obtain ⟨cut, hzero, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun B : ChartBall I U => B.isOpen_core.preimage γ.continuous)
      (show univ ⊆ ⋃ B : ChartBall I U, γ ⁻¹' B.core from
        fun t _ => by obtain ⟨B, hB⟩ := hc t; exact mem_iUnion.mpr ⟨B, hB⟩)
  choose B hB using hsub
  exact ⟨⟨n + 1, Nat.succ_pos n, cut, hzero, hn _ (Nat.le_succ n), hmono,
    fun i => B i, fun i => hB i⟩⟩


theorem exists_compact_path_subdivision [I.Boundaryless] {U : Set M} (hU : IsOpen U)
    (hconn : IsConnected U) {p q : M} (hp : p ∈ U) (hq : q ∈ U) :
    ∃ γ : Path p q, IsCompact (range γ) ∧ range γ ⊆ U ∧
      Nonempty (Subdivision (I := I) (U := U) γ) := by
  obtain ⟨γ, hcompact, hγ⟩ := exists_compact_path (I := I) hU hconn hp hq
  exact ⟨γ, hcompact, hγ, exists_subdivision hU γ hγ⟩

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple.ChartChain
