import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.SourceInteriorPairChart
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryCharts.AtlasPatch
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.CenteredHalfspaceCharts
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall

/-!
# Complete local pair charts of an original-atlas proper disk

The supplied disk and its exact old-boundary incidence produce the
actual local pair charts at every point. No pair chart, collar or
global Euclidean model of the ambient space is assumed. See rigidity
derivation012, sections3--5.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

/-- An actual proper polyhedral disk in the original atlas has
complete plane or boundary half-plane charts. Both transition
directions and the whole original disk image are retained.
See rigidity derivation012. -/
theorem exists_original_proper_disk_pair_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    (he : PLDomain e R) {j : V2 → X}
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R)
    (hproper : ∀ z : D, j z ∈ frontier R ↔ (z : V2) ∈ Q)
    (z : D) :
    ∃ H : OpenPartialHomeomorph X C3,
      j z ∈ H.source ∧ H.target = interior (CoordinateHalfBoxes.box 1) ∧
      H (j z) = 0 ∧
      (∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans H) ((e i).symm.trans H).source ∧
        LocallyPiecewiseAffineOn (H.symm.trans (e i)) (H.symm.trans (e i)).source) ∧
      ((H.source ⊆ interior R ∧
        ∀ x ∈ H.source, x ∈ j '' D ↔ (H x).2 = 0) ∨
       ((∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1) ∧
        ∀ x ∈ H.source, x ∈ j '' D ↔ 0 ≤ (H x).1.1 ∧ (H x).2 = 0)) := by
  obtain ⟨_, _, _, _, _, _, hmodel, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  obtain ⟨_, ⟨K, hK, hKD, _⟩, _⟩ := hmodel
  have hjK : PolyhedralPLInCharts e j K.space := hKD.symm ▸ hj
  have hembK : Topology.IsEmbedding (fun x : K.space => j x) := by
    exact hemb.comp (Homeomorph.setCongr hKD).isEmbedding
  let zK : K.space := ⟨z, hKD.symm.subset z.property⟩
  by_cases hz : (z : V2) ∈ Q
  · obtain ⟨G, A, hzG, hGz, hA, hGcompat, hGhalf, hGfront⟩ :=
      he.exists_centered_boundary_chart ((hproper z).mpr hz)
    obtain ⟨H, B, hzH, hHz, hB, _, hHi, hHhalf, hHrim⟩ :=
      exists_centered_disk_rim_chart hz
    have hhalf : ∀ x ∈ H.source, x ∈ K.space ↔ 0 ≤ B (H x) := by
      simpa only [hKD] using hHhalf
    have hpositive (x : V2) (hx : x ∈ K.space) (hxG : j x ∈ G.source) :
        0 ≤ A (G (j x)) := (hGhalf (j x) hxG).mp (hDR (hKD.subset hx))
    have hzero (x : V2) (hx : x ∈ K.space) (hxH : x ∈ H.source)
        (hxG : j x ∈ G.source) : A (G (j x)) = 0 ↔ B (H x) = 0 :=
      (hGfront (j x) hxG).symm.trans
        ((hproper ⟨x, hKD.subset hx⟩).trans (hHrim x hxH))
    obtain ⟨C, hzC, hCG, hCt, hCz, hCA, hCS, hCcompat⟩ :=
      exists_original_boundary_source_pair_chart K hK hjK hembK zK H hzH hHz hHi
        B hB hhalf G hGcompat hzG hGz A hA hpositive hzero
    refine ⟨C, hzC, hCt, hCz, hCcompat, Or.inr ⟨?_, ?_⟩⟩
    · intro x hx
      exact (hGhalf x (hCG hx)).trans (hCA x hx)
    · simpa only [hKD] using hCS
  · have hzint : (z : V2) ∈ interior D := by
      by_contra hnot
      have hfront : (z : V2) ∈ frontier D :=
        isClosed_closedBall.frontier_eq.symm.subset ⟨z.property, hnot⟩
      rw [frontier_closedBall _ one_ne_zero] at hfront
      exact hz hfront
    have hjzint : j z ∈ interior R := by
      by_contra hnot
      exact hz ((hproper z).mp
        (he.closed.frontier_eq.symm.subset ⟨hDR z.property, hnot⟩))
    obtain ⟨i, hi⟩ := he.cover (j z)
    have hzKint : (zK : V2) ∈ interior K.space := by
      simpa only [hKD] using hzint
    obtain ⟨H, hzH, hHsource, hHt, hHz, hHS, hHcompat⟩ :=
      exists_original_interior_disk_pair_chart K hK hjK hembK (e i)
        (fun a => he.compatible a i) zK hzKint hi isOpen_interior hjzint
    refine ⟨H, hzH, hHt, hHz, hHcompat, Or.inl ⟨?_, ?_⟩⟩
    · exact fun x hx => (hHsource hx).1
    · simpa only [hKD] using hHS

end PoincareMT.M76
