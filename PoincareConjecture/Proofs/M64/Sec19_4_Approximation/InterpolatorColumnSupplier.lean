import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorVerticalColumn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

omit [T2Space M] in

theorem m64_cell_side_short_of_polygon_short
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {N : ℕ} (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {r : ℝ}
    (hshort : ∀ x : ℝ,
      g.edist (gamma x) (polygon.map x) < ENNReal.ofReal r)
    (j : Fin N) {z : LoopPlane}
    (hz : z ∈ m64PolygonCellSet j) :
    g.edist (gamma (z 0)) ((polygon.side j).map
      (z 0 - m63CellLeft N j)) < ENNReal.ofReal r := by
  have hs : z 0 - m63CellLeft N j ∈
      Icc (0 : ℝ) (m63CellLength N) := by
    change m63CellLeft N j ≤ z 0 ∧
      z 0 ≤ m63CellLeft N j + m63CellLength N ∧
        0 ≤ z 1 ∧ z 1 ≤ 1 at hz
    constructor
    · exact sub_nonneg.mpr hz.1
    · linarith [hz.2.1]
  have hc := polygon.cell_agreement j (z 0 - m63CellLeft N j) hs
  rw [← hc]
  rw [show m63CellLeft N j + (z 0 - m63CellLeft N j) = z 0 by ring]
  exact hshort (z 0)

omit [T2Space M] in

theorem m64_interpolator_vertical_column_of_global_short
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {N : ℕ} (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {U : Set (M × M)} {H : ℝ × (M × M) → M}
    (hU : IsOpen U)
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma Set.univ)
    (hpair : ∀ j : Fin N, ∀ p ∈ m64PolygonCellSet j,
      (gamma (p 0), (polygon.side j).map
        (p 0 - m63CellLeft N j)) ∈ U)
    (j : Fin N) {x : LoopPlane}
    (hx : x ∈ interior (m64PolygonCellSet j))
    {r : ℝ}
    (hshort : ∀ y : ℝ,
      g.edist (gamma y) (polygon.map y) < ENNReal.ofReal r)
    (hgeom : g.edist (gamma (x 0)) ((polygon.side j).map
      (x 0 - m63CellLeft N j)) < ENNReal.ofReal r →
      H (0, gamma (x 0), (polygon.side j).map
        (x 0 - m63CellLeft N j)) = gamma (x 0) ∧
      H (1, gamma (x 0), (polygon.side j).map
        (x 0 - m63CellLeft N j)) =
          (polygon.side j).map (x 0 - m63CellLeft N j) ∧
      g.IsGeodesicOn
        (fun t => H (t, gamma (x 0), (polygon.side j).map
          (x 0 - m63CellLeft N j))) (Ioo (-1 : ℝ) 2) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm
          (H (t, gamma (x 0), (polygon.side j).map
            (x 0 - m63CellLeft N j)))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
            (fun s => H (s, gamma (x 0), (polygon.side j).map
              (x 0 - m63CellLeft N j))) t 1) =
            (g.edist (gamma (x 0)) ((polygon.side j).map
              (x 0 - m63CellLeft N j))).toReal) ∧
      g.pathELength
        (fun t => H (t, gamma (x 0), (polygon.side j).map
          (x 0 - m63CellLeft N j))) 0 1 =
        g.edist (gamma (x 0)) ((polygon.side j).map
          (x 0 - m63CellLeft N j))) :
    g.tangentNorm
      (H (x 1, gamma (x 0), (polygon.side j).map
        (x 0 - m63CellLeft N j)))
      (mfderiv (𝓡 2) (𝓡 3)
        (fun p : LoopPlane => H (p 1, gamma (p 0),
          (polygon.side j).map (p 0 - m63CellLeft N j))) x
        (EuclideanSpace.basisFun (Fin 2) ℝ 1)) =
      (g.edist (gamma (x 0)) ((polygon.side j).map
        (x 0 - m63CellLeft N j))).toReal := by
  apply m64_interpolator_vertical_column_of_speed polygon hU hH hgamma hpair j
    (interior_subset hx)
    (m64_cell_side_short_of_polygon_short polygon hshort j
      (interior_subset hx))
    hgeom

end PoincareConjecture
