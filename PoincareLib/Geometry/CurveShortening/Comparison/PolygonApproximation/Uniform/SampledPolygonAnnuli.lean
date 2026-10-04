import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Sampled.InterpolatorAnnulus
import PoincareLib.Geometry.CurveShortening.Comparison.PolygonApproximation.Uniform.InterpolatorHorizontal
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Two.EndpointMinimizingInterpolator

/-!
# Uniformly small annuli for every sufficiently fine sampled polygon

The compact family gives one speed bound. The fixed M63 interpolator gives
one horizontal derivative bound on a compact short-pair tube. Its vertical
speed is bounded by the mesh size, so one threshold works for every larger
polygon count and every family member.

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

/-- Choose one count threshold giving strict-area geodesic annuli for every sampled polygon
in the compact family. Source: Auxiliary step for MT Definition 19.18 and Claims
19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_uniform_sampled_polygon_annuli
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (univ : Set M))
    {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (Gamma : Z → C1FreeLoopSpace (M := M)) (hGamma : Continuous Gamma)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ z : Z,
      ∀ polygon : M63GeodesicPolygon g D N,
        M64SampledPolygon (Gamma z) polygon →
        ∃ A : M64Annulus g (periodicFreeLoop (Gamma z)) polygon.map,
          M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
            0 ≤ A.area ∧ A.area < zeta := by
  obtain ⟨r, hr, H, hH, hgeom, _hdiag, _hunique⟩ :=
    M63.exists_smooth_minimizing_interpolator g hcompact
  have hprops : ∀ p q : M, g.edist p q < ENNReal.ofReal r →
      H (0, p, q) = p ∧ H (1, p, q) = q ∧
      g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm (H (t, p, q))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => H (s, p, q)) t 1) =
            (g.edist p q).toReal) ∧
      g.pathELength (fun t => H (t, p, q)) 0 1 = g.edist p q := by
    intro p q hpq
    obtain ⟨h0, h1, hgeo, hs, hlen, _⟩ := hgeom p q hpq
    exact ⟨h0, h1, hgeo, hs, hlen⟩
  obtain ⟨S, hS, hspeed⟩ := m64_compact_family_speed_bound g Gamma hGamma
  obtain ⟨B, hB, NH, hNH, hhor⟩ :=
    m64_uniform_interpolator_horizontal_bound g D hcompact hr H hH Gamma hGamma
  have hdenom : 0 < B * volume.real m64AnnulusDomain + 1 := by
    positivity
  obtain ⟨NA, hNA, hmesh⟩ := m64_exists_mesh_threshold (S := S)
    (div_pos hzeta hdenom)
  refine ⟨max NH NA, hNH.trans_le (le_max_left _ _), ?_⟩
  intro N hN0N z polygon hsampled
  have hNHN : NH ≤ N := (le_max_left _ _).trans hN0N
  have hNAN : NA ≤ N := (le_max_right _ _).trans hN0N
  have hN : 0 < N := hNH.trans_le hNHN
  obtain ⟨hshortHalf, hcol0⟩ := hhor N hNHN z polygon hsampled
  have hshort : ∀ x : ℝ,
      g.edist (periodicFreeLoop (Gamma z) x) (polygon.map x) <
        ENNReal.ofReal r := by
    intro x
    exact (hshortHalf x).trans
      ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
  have hK1 : 0 ≤ 2 * S * m63CellLength N :=
    mul_nonneg (mul_nonneg (by norm_num) hS) (m63CellLength_pos hN).le
  have hstrict : B * (2 * S * m63CellLength N) * volume.real m64AnnulusDomain <
      zeta := by
    calc
      B * (2 * S * m63CellLength N) * volume.real m64AnnulusDomain =
          (B * volume.real m64AnnulusDomain) * (2 * S * m63CellLength N) := by ring
      _ ≤ (B * volume.real m64AnnulusDomain + 1) * (2 * S * m63CellLength N) :=
        mul_le_mul_of_nonneg_right (by linarith) hK1
      _ < zeta := by
        simpa only [mul_comm] using (lt_div_iff₀ hdenom).mp (hmesh N hNAN)
  exact m64_sampled_interpolator_annulus g D hS hB H hH hprops hN
    (Gamma z) polygon hsampled (hspeed z) hshort hcol0 hstrict

/-- Specialize the uniform sampled-annulus construction to an arbitrary compact set of C1
loops. Source: Auxiliary step for MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453;
project construction in `proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_uniform_compact_sampled_polygon_annuli
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcompact : IsCompact (univ : Set M))
    (X : Set (C1FreeLoopSpace (M := M))) (hX : IsCompact X)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ gamma : C1FreeLoopSpace (M := M), gamma ∈ X →
        ∀ polygon : M63GeodesicPolygon g D N,
          M64SampledPolygon gamma polygon →
          ∃ A : M64Annulus g (periodicFreeLoop gamma) polygon.map,
            M64PiecewiseC1Annulus A ∧ M64GeodesicAnnulus D A ∧
              0 ≤ A.area ∧ A.area < zeta := by
  let : CompactSpace X := isCompact_iff_compactSpace.mp hX
  obtain ⟨N0, hN0, hannulus⟩ := m64_uniform_sampled_polygon_annuli
    g D hcompact (fun gamma : X => gamma.1) continuous_subtype_val hzeta
  exact ⟨N0, hN0, fun N hN gamma hgamma polygon hsampled =>
    hannulus N hN ⟨gamma, hgamma⟩ polygon hsampled⟩

end PoincareMT
