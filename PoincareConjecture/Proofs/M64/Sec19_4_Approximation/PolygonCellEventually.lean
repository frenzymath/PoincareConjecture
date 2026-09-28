import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64_polygon_map_eventuallyEq_side_of_cell_interior
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (polygon : M63GeodesicPolygon g D N)
    (j : Fin N) {x : LoopPlane}
    (hx : x ∈ interior (m64PolygonCellSet j)) :
    ∀ᶠ p in 𝓝 x,
      polygon.map (p 0) =
        (polygon.side j).map (p 0 - m63CellLeft N j) := by
  have hnhds : ∀ᶠ p in 𝓝 x, p ∈ interior (m64PolygonCellSet j) :=
    isOpen_interior.mem_nhds hx
  filter_upwards [hnhds] with p hp
  have hpcell : p ∈ m64PolygonCellSet j := interior_subset hp
  have hs : p 0 - m63CellLeft N j ∈
      Icc (0 : ℝ) (m63CellLength N) := by
    change m63CellLeft N j ≤ p 0 ∧
      p 0 ≤ m63CellLeft N j + m63CellLength N ∧
        0 ≤ p 1 ∧ p 1 ≤ 1 at hpcell
    constructor
    · exact sub_nonneg.mpr hpcell.1
    · linarith [hpcell.2.1]
  have hc := polygon.cell_agreement j (p 0 - m63CellLeft N j) hs
  convert hc using 1
  ring_nf

theorem m64_interpolator_map_eventuallyEq_cell_extension
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {H : ℝ × (M × M) → M}
    (j : Fin N) {x : LoopPlane}
    (hx : x ∈ interior (m64PolygonCellSet j)) :
    (fun p : LoopPlane => H (p 1, gamma (p 0), polygon.map (p 0))) =ᶠ[𝓝 x]
      (fun p : LoopPlane => H (p 1, gamma (p 0),
        (polygon.side j).map (p 0 - m63CellLeft N j))) := by
  filter_upwards [m64_polygon_map_eventuallyEq_side_of_cell_interior
      polygon j hx] with p hp
  rw [hp]

end PoincareConjecture
