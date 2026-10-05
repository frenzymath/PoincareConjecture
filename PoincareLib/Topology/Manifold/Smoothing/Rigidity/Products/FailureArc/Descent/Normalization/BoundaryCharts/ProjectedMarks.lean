import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryCharts.ProjectedBranches
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Coordinates.Mathlib.SupportedChartRegion

/-!
# Original boundary markings in a projected branch chart

A relatively open original frontier mark determines an actual open lower
window. On this window, and on its whole upper inverse image, the complete
frontier equals the original mark. The window may be intersected with any
prescribed open support before constructing the annulus branch chart.
-/

set_option autoImplicit false

open Set Topology Geometry

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}

/-- Restrict an actual lower neighborhood to the original relatively open
boundary mark, preserving the full marked frontier on both levels. -/
theorem Step.exists_open_boundary_mark_window
    (step : Step s t) {R Fmark : Set M}
    (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    (x : t.Carrier) (hx : t.projection x ∈ Fmark)
    {O : Set s.Carrier} (hO : IsOpen O)
    (hxO : step.projection (step.inclusion x) ∈ O) :
    ∃ W : Set s.Carrier, IsOpen W ∧ W ⊆ O ∧
      step.projection (step.inclusion x) ∈ W ∧
      (s.projection ⁻¹' Fmark) ∩ W = frontier (s.projection ⁻¹' R) ∩ W ∧
      (t.projection ⁻¹' Fmark) ∩ ((step.projection ∘ step.inclusion) ⁻¹' W) =
        frontier (t.projection ⁻¹' R) ∩
          ((step.projection ∘ step.inclusion) ⁻¹' W) := by
  obtain ⟨V, hV, hFV⟩ := exists_open_frontier_mark hF hopen
  let W := O ∩ s.projection ⁻¹' V
  have hW : IsOpen W := hO.inter (hV.preimage s.projection.continuous)
  have hxW : step.projection (step.inclusion x) ∈ W := by
    refine ⟨hxO, ?_⟩
    change s.projection (step.projection (step.inclusion x)) ∈ V
    rw [← step.original_eq]
    exact (hFV.subset hx).2
  have hlower : (s.projection ⁻¹' Fmark) ∩ W =
      frontier (s.projection ⁻¹' R) ∩ W := by
    rw [hFV, preimage_inter, s.frontier_region R]
    ext y
    change (s.projection y ∈ frontier R ∧ s.projection y ∈ V) ∧
      (y ∈ O ∧ s.projection y ∈ V) ↔
        s.projection y ∈ frontier R ∧ (y ∈ O ∧ s.projection y ∈ V)
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2⟩⟩
  refine ⟨W, hW, inter_subset_left, hxW, hlower, ?_⟩
  rw [step.region_preimage Fmark, step.frontier_preimage R,
    ← preimage_inter, ← preimage_inter, hlower]

/-- Any exact frontier chart inside the marked window also has an exact
equation for the original mark. This applies to the constructed annulus
chart, independently of its chosen coordinate basis. -/
theorem Stage.boundary_mark_chart_iff
    {R Fmark : Set M} {W : Set s.Carrier}
    (hmark : (s.projection ⁻¹' Fmark) ∩ W = frontier (s.projection ⁻¹' R) ∩ W)
    (Q : OpenPartialHomeomorph s.Carrier V3) (hQW : Q.source ⊆ W)
    (g : V3 → ℝ)
    (hfront : ∀ y ∈ Q.source, y ∈ frontier (s.projection ⁻¹' R) ↔ g (Q y) = 0) :
    ∀ y ∈ Q.source, s.projection y ∈ Fmark ↔ g (Q y) = 0 := by
  intro y hy
  have hm : s.projection y ∈ Fmark ↔ y ∈ frontier (s.projection ⁻¹' R) := by
    constructor
    · intro h
      exact (hmark.subset ⟨h, hQW hy⟩).1
    · intro h
      exact (hmark.symm.subset ⟨h, hQW hy⟩).1
  exact hm.trans (hfront y hy)

end Geometry.OriginalPLTower
