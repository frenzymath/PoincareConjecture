import PoincareLib.Topology.Manifold.Smoothing.CompactCore.General.Mathlib.FiniteSourcePL
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.RelativeManifoldPLApproximation
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.FinitePLIntervals
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.AtlasOfCover
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# An actual PL path in a prescribed open component

The original covering atlas supplies local path connectedness and
local compactness. Relative approximation fixes the complete two-point
endpoint set and keeps the whole path in the original open component.
See Hudson1969, pp.15--19, and Wall011, section2.
-/

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

/-- Two points of a connected open region in an actual PL atlas are
joined by a chartwise PL path contained in that same region, with both
endpoint values fixed exactly. See Wall011, section2. -/
theorem exists_polyhedralPL_path_in_open
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    {U : Set X} (hU : IsOpen U) (hconn : IsConnected U)
    {a b : X} (ha : a ∈ U) (hb : b ∈ U) :
    ∃ q : ℝ → X, PolyhedralPLInCharts e q (Icc (0 : ℝ) 1) ∧
      q 0 = a ∧ q 1 = b ∧ MapsTo q (Icc (0 : ℝ) 1) U := by
  classical
  let := ChartedSpace.ofChartCover e hcover
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace F X
  let : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace F X
  obtain ⟨p, hpU⟩ := (hU.isConnected_iff_isPathConnected.mp hconn).joinedIn a ha b hb
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI
  obtain ⟨L, hL, hLs⟩ := ({0, 1} : Set ℝ).toFinite.exists_finite_geometric_carrier
  have hLK : L.space ⊆ K.space := by
    rw [hLs, hKs]
    intro x hx
    rcases mem_insert_iff.mp hx with rfl | hx
    · exact ⟨le_rfl, zero_le_one⟩
    · rcases mem_singleton_iff.mp hx with rfl
      exact ⟨zero_le_one, le_rfl⟩
  have hpK : ContinuousOn p.extend K.space := p.continuous_extend.continuousOn
  have hpL : PolyhedralPLInCharts e p.extend L.space := by
    rw [hLs]
    exact polyhedralPLInCharts_of_finite e hcover p.extend ({0, 1} : Set ℝ).toFinite
  have hpKU : MapsTo p.extend K.space U := by
    intro x hx
    have hxI : x ∈ Icc (0 : ℝ) 1 := hKs.subset hx
    rw [p.extend_apply hxI]
    exact hpU ⟨x, hxI⟩
  obtain ⟨q, hq, hfix, hqU, _⟩ := exists_relative_polyhedralPL_approximation
    e hcompat hcover K L hK hL hLK hpK hpL hU hpKU
  refine ⟨q, hKs ▸ hq, ?_, ?_, fun _ hx => hqU (hKs.symm.subset hx)⟩
  · exact (hfix (hLs.symm.subset (by simp))).trans p.extend_zero
  · exact (hfix (hLs.symm.subset (by simp))).trans p.extend_one

end OpenPartialHomeomorph
