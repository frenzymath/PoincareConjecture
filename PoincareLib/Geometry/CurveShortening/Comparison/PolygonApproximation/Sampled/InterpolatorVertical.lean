import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Interpolator.ColumnSupplier
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Interpolator.VerticalColumnAE
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Uniform.SampledPolygonCloseness

/-!
# The vertical interpolator column tends to zero

The vertical column is the constant speed of the minimizing segment from
the source loop to its sampled polygon.  The source speed bound therefore
controls this column by twice the polygon mesh length.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- Endpoint pairs at strictly bounded Riemannian extended distance form an open set.
Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project
construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_isOpen_short_pair_tube (g : RiemannianMetric 3 M) (r : ℝ) :
    IsOpen {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r} := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace LoopAmbient M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  exact isOpen_lt continuous_edist continuous_const

/-- The sampled interpolator's vertical column is bounded by twice the source speed times
cell length. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp.
450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_sampled_interpolator_vertical_column_bound
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {r S : ℝ} (hS : 0 ≤ S) (H : ℝ × (M × M) → M)
    (hH : ContMDiffOn
      (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ
        {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r}))
    (hprops : ∀ p q : M, g.edist p q < ENNReal.ofReal r →
      H (0, p, q) = p ∧ H (1, p, q) = q ∧
      g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm (H (t, p, q))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => H (s, p, q)) t 1) =
            (g.edist p q).toReal) ∧
      g.pathELength (fun t => H (t, p, q)) 0 1 = g.edist p q)
    {N : ℕ} (hN : 0 < N) (gamma : C1FreeLoopSpace (M := M))
    (polygon : M63GeodesicPolygon g D N)
    (hsampled : M64SampledPolygon gamma polygon)
    (hbound : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      g.tangentNorm (periodicFreeLoop gamma x)
        (curveVelocity (periodicFreeLoop gamma) x) ≤ S)
    (hshort : ∀ x : ℝ,
      g.edist (periodicFreeLoop gamma x) (polygon.map x) < ENNReal.ofReal r) :
    ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      g.tangentNorm (H (z 1, periodicFreeLoop gamma (z 0), polygon.map (z 0)))
        (mfderiv (𝓡 2) (𝓡 3)
          (fun p : LoopPlane => H (p 1, periodicFreeLoop gamma (p 0),
            polygon.map (p 0))) z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤
              2 * S * m63CellLength N := by
  have hpair : ∀ j : Fin N, ∀ p ∈ m64PolygonCellSet j,
      (periodicFreeLoop gamma (p 0), (polygon.side j).map
        (p 0 - m63CellLeft N j)) ∈
          {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r} := by
    intro j p hp
    exact m64_cell_side_short_of_polygon_short polygon hshort j hp
  apply m64_interpolator_vertical_column_ae_of_cell_extensions hN polygon rfl
  intro j z hz
  rw [m64_interpolator_vertical_column_of_global_short polygon
    (m64_isOpen_short_pair_tube g r) hH
    (Proofs.M58.contMDiff_periodicFreeLoop gamma).contMDiffOn hpair j hz hshort
    (hprops _ _)]
  have hpoly := (m64_polygon_map_eventuallyEq_side_of_cell_interior polygon j hz).self_of_nhds
  rw [← hpoly]
  apply ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg (by norm_num) hS) (m63CellLength_pos hN).le)
  exact m64_sampled_polygon_edist_le hN polygon
    (Proofs.M58.contMDiff_periodicFreeLoop gamma)
    (Proofs.M58.periodic_periodicFreeLoop gamma) hsampled hS hbound (z 0)

end PoincareMT
