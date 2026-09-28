import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryCharts.AtlasPatch
import PoincareConjecture.Proofs.M76.Rigidity.SourceDiskPairCharts
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_original_locally_proper_disk_pair_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R U : Set X}
    (he : PLDomain e R) {j : V2 → X}
    (hj : PolyhedralPLInCharts e j D)
    (hemb : Topology.IsEmbedding (fun z : D => j z))
    (hDR : MapsTo j D R) (hU : IsOpen U)
    (hproper : ∀ z : D, j z ∈ U → (j z ∈ frontier R ↔ (z : V2) ∈ Q))
    (z : D) (hzU : j z ∈ U) :
    ∃ H : OpenPartialHomeomorph X C3,
      j z ∈ H.source ∧ H.source ⊆ U ∧
      H.target = interior (CoordinateHalfBoxes.box 1) ∧ H (j z) = 0 ∧
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
  have hembK : Topology.IsEmbedding (fun x : K.space => j x) :=
    hemb.comp (Homeomorph.setCongr hKD).isEmbedding
  let zK : K.space := ⟨z, hKD.symm.subset z.property⟩
  by_cases hz : (z : V2) ∈ Q
  · obtain ⟨G₀, A, hzG₀, hG₀z, hA, hG₀compat, hG₀half, hG₀front⟩ :=
      he.exists_centered_boundary_chart ((hproper z hzU).mpr hz)
    let G := G₀.restrOpen U hU
    have hGcompat (i : ι) : (e i).symm.trans G ∈ piecewiseAffineGroupoid V3 :=
      (e i).piecewiseAffine_compatible_restrOpen_right G₀ (hG₀compat i) hU
    obtain ⟨H, B, hzH, hHz, hB, _, hHi, hHhalf, hHrim⟩ :=
      exists_centered_disk_rim_chart hz
    have hhalf : ∀ x ∈ H.source, x ∈ K.space ↔ 0 ≤ B (H x) := by
      simpa only [hKD] using hHhalf
    have hpositive (x : V2) (hx : x ∈ K.space) (hxG : j x ∈ G.source) :
        0 ≤ A (G (j x)) := (hG₀half (j x) hxG.1).mp (hDR (hKD.subset hx))
    have hzero (x : V2) (hx : x ∈ K.space) (hxH : x ∈ H.source)
        (hxG : j x ∈ G.source) : A (G (j x)) = 0 ↔ B (H x) = 0 :=
      (hG₀front (j x) hxG.1).symm.trans
        ((hproper ⟨x, hKD.subset hx⟩ hxG.2).trans (hHrim x hxH))
    obtain ⟨C, hzC, hCG, hCt, hCz, hCA, hCS, hCcompat⟩ :=
      exists_original_boundary_source_pair_chart K hK hjK hembK zK H hzH hHz hHi
        B hB hhalf G hGcompat ⟨hzG₀, hzU⟩ hG₀z A hA hpositive hzero
    refine ⟨C, hzC, fun _ hx => (hCG hx).2, hCt, hCz, hCcompat, Or.inr ⟨?_, ?_⟩⟩
    · intro x hx
      exact (hG₀half x (hCG hx).1).trans (hCA x hx)
    · simpa only [hKD] using hCS
  · have hzint : (z : V2) ∈ interior D := by
      by_contra hnot
      have hfront : (z : V2) ∈ frontier D :=
        isClosed_closedBall.frontier_eq.symm.subset ⟨z.property, hnot⟩
      rw [frontier_closedBall _ one_ne_zero] at hfront
      exact hz hfront
    have hjzint : j z ∈ interior R := by
      by_contra hnot
      exact hz ((hproper z hzU).mp
        (he.closed.frontier_eq.symm.subset ⟨hDR z.property, hnot⟩))
    obtain ⟨i, hi⟩ := he.cover (j z)
    have hzKint : (zK : V2) ∈ interior K.space := by
      simpa only [hKD] using hzint
    obtain ⟨H, hzH, hHsource, hHt, hHz, hHS, hHcompat⟩ :=
      exists_original_interior_disk_pair_chart K hK hjK hembK (e i)
        (fun a => he.compatible a i) zK hzKint hi (hU.inter isOpen_interior)
        ⟨hzU, hjzint⟩
    refine ⟨H, hzH, fun _ hx => (hHsource hx).1.1, hHt, hHz, hHcompat,
      Or.inl ⟨fun _ hx => (hHsource hx).1.2, ?_⟩⟩
    simpa only [hKD] using hHS

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior
