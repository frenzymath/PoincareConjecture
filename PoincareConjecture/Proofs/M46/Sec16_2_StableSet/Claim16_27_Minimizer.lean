import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_LowScalarPoint
import PoincareConjecture.Proofs.M14.Sec6_1_LLength

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

theorem MinimizingRegion.all_minimizers_in_cage
    {X : Type u} [TopologicalSpace X] {time : X → ℝ} {I : SpacetimeInterval}
    {G : GeneralizedLGeometryTransport 3 X time I} {T start : ℝ} {x y : G.Point}
    {confinement : ActionConfinement G T start x}
    (M : MinimizingRegion G T start x confinement) (hy : y ∈ M.region)
    (path : M14BackwardPath G T 0 (T - G.spacetime.timeFunction y) x y)
    (hmin : M14IsMinimizing path) :
    MapsTo path.curve (Icc 0 (T - G.spacetime.timeFunction y)) confinement.cage := by
  obtain ⟨htime, competitor, hcompetitor⟩ := (M.region_exact y).mp hy
  exact confinement.paths_mem _ (sub_pos.mpr htime.2)
    (sub_le_sub_left htime.1 T) y path ((hmin competitor).trans_lt hcompetitor)

theorem MinimizingRegion.short_path
    {X : Type u} [TopologicalSpace X] {time : X → ℝ} {I : SpacetimeInterval}
    {G : GeneralizedLGeometryTransport 3 X time I} {T start : ℝ} {x : G.Point}
    {confinement : ActionConfinement G T start x}
    (M : MinimizingRegion G T start x confinement) (hstart : start < T) :
    ∃ y : G.Point, ∃ path : M14BackwardPath G T 0 (T - start) x y,
      M14IsMinimizing path ∧
      M14BackwardLAction G path ≤ 3 * Real.sqrt (T - start) ∧
      MapsTo path.curve (Icc 0 (T - start)) confinement.cage := by
  obtain ⟨y, hy, hytime, haction, _⟩ := M.slice_minimum start ⟨le_rfl, hstart⟩
  have hpath : ∃ path : M14BackwardPath G T 0 (T - start) x y,
      M14IsMinimizing path := by
    rw [← hytime]
    exact M.minimizing y hy
  obtain ⟨path, hmin⟩ := hpath
  have hshort : M14BackwardLAction G path ≤ 3 * Real.sqrt (T - start) := by
    rw [M14.action_eq_actionValue_of_minimizing path hmin]
    exact haction
  exact ⟨y, path, hmin, hshort, confinement.paths_mem _ (sub_pos.mpr hstart)
    le_rfl y path (hshort.trans_lt confinement.barrier_large)⟩

theorem regular_history_scalar_lower (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O)
    {window : M33RegularHistoryWindow F} (R : M46RegularSpacetimeData window)
    {t : ℝ} (htobs : t ∈ surgeryObservationInterval O)
    (ht : t ∈ R.history.generalized.interval)
    (y : (R.history.generalized.slice t).carrier) :
    -6 ≤ horizontalScalarCurvature R.geometry.toLGeometry.leafwise
      (⟨t, y⟩ : R.history.generalized.point) := by
  have hp := old.pinched t htobs (O.interval_subset htobs)
  have htzero : 0 ≤ t := hp.1
  have hden : 0 < 1 + 4 * t := by positivity
  have hfloor : -6 ≤ -6 / (1 + 4 * t) := (le_div_iff₀ hden).mpr (by nlinarith)
  change -6 ≤ horizontalScalarCurvature R.geometry.leafwise
    (⟨t, y⟩ : R.history.generalized.point)
  rw [M13.originalSlice_scalar R.geometry P.m13 t y,
    ← R.history.scalar_pullback t ht y]
  exact hfloor.trans (hp.2.1 _ (mem_univ _))

theorem regular_history_path_scalar_lower (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} {p : SurgeryParameterPrefix K}
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O)
    {window : M33RegularHistoryWindow F} (R : M46RegularSpacetimeData window)
    {T S : ℝ} {x y : R.geometry.toLGeometry.Point}
    (path : M14BackwardPath R.geometry.toLGeometry T 0 S x y)
    (hT : T ∈ surgeryObservationInterval O) (hS : S ≤ T)
    (hwindow : Icc (T - S) T ⊆ R.history.generalized.interval) :
    ∀ s ∈ Icc 0 S,
      -6 ≤ horizontalScalarCurvature R.geometry.toLGeometry.leafwise (path.curve s) := by
  intro s hs
  have hclock : (path.curve s).1 = T - s := path.curve_time s hs
  have htobs : (path.curve s).1 ∈ surgeryObservationInterval O := by
    change 0 ≤ (path.curve s).1 ∧ (path.curve s).1 < O.H
    change 0 ≤ T ∧ T < O.H at hT
    rw [hclock]
    constructor <;> linarith [hs.1, hs.2]
  have ht : (path.curve s).1 ∈ R.history.generalized.interval := by
    apply hwindow
    rw [hclock]
    constructor <;> linarith [hs.1, hs.2]
  exact regular_history_scalar_lower P old R htobs ht (path.curve s).2

end PoincareConjecture.Proofs.M46
