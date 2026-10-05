import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Polygon.CellLipschitzGlue
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Interpolator.LocalLipschitz
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Interpolator.MapFields

/-!
# Lipschitz regularity of the interpolator rectangle

On each closed polygon cell the assembled map agrees with its smooth side
extension.  Compact-cell estimates and finite-strip gluing give a global
rectangle estimate, including the polygon cuts.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- The cell extensions glue to a Lipschitz map on the entire closed annulus rectangle.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_interpolator_rectangle_lipschitz
    (g : RiemannianMetric n M) {D : LeviCivitaData g}
    {N : ℕ} (hN : 0 < N) (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {U : Set (M × M)} {H : ℝ × (M × M) → M}
    (hU : IsOpen U)
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    (hpair_global : ∀ x : ℝ, (gamma x, polygon.map x) ∈ U) :
    ∃ K : ℝ≥0, ∀ x y : m64AnnulusDomain,
      g.edist (H (x.1 1, gamma (x.1 0), polygon.map (x.1 0)))
        (H (y.1 1, gamma (y.1 0), polygon.map (y.1 0))) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
  let f : LoopPlane → M := fun p => H (p 1, gamma (p 0), polygon.map (p 0))
  have hcontinuous : ContinuousOn f m64AnnulusDomain :=
    m64_interpolator_map_continuous polygon hH hgamma.continuous hpair_global f rfl
  have hside (j : Fin N) (p : LoopPlane) (hp : p ∈ m64PolygonCellSet j) :
      polygon.map (p 0) = (polygon.side j).map (p 0 - m63CellLeft N j) := by
    have hs : p 0 - m63CellLeft N j ∈ Icc (0 : ℝ) (m63CellLength N) := by
      constructor <;> linarith [hp.1, hp.2.1]
    have heq := polygon.cell_agreement j (p 0 - m63CellLeft N j) hs
    simpa only [add_sub_cancel] using heq
  have hpair : ∀ j : Fin N, ∀ p ∈ m64PolygonCellSet j,
      (gamma (p 0), (polygon.side j).map (p 0 - m63CellLeft N j)) ∈ U := by
    intro j p hp
    rw [← hside j p hp]
    exact hpair_global (p 0)
  apply m64Annulus_hLip_of_polygon_cells g (f := f) hN
  intro j
  exact m64_polygon_cell_lipschitz_of_extension g hN j hcontinuous
    (fun _ hx => m64_interpolator_contMDiffAt_of_cell polygon hU hH
      hgamma.contMDiffOn hpair j hx)
    (fun p hp => by
      change H (p 1, gamma (p 0), polygon.map (p 0)) = _
      rw [hside j p hp])

end PoincareMT
