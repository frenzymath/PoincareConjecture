import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapBandRadialRays
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterFans









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition

variable {S : Type*} [TopologicalSpace S]
  [T2Space S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {D : FiniteChartRegionDecomposition (M := S)}
  {P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius (p : S)}
  {region : D.vertices → Bool × Bool → D.regions} {chart : D.regions → S}
  {caps : ∀ p, ChartCircleArrangementVertexPatch.VertexCapFaces (P p)
    (fun s => chart (region p s))}

namespace CapGraphEndpoint

variable {e : D.EdgeIndex} {R₀ R₁ : D.regions} {a₀ b₀ a₁ b₁ trim : ℝ} {terminal : Bool}
  {G₀ : D.OrientedGraphPiece e R₀ (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R₀)).symm a₀ b₀}
  {G₁ : D.OrientedGraphPiece e R₁ (chartAt (EuclideanSpace ℝ (Fin 2)) (chart R₁)).symm a₁ b₁}
  (E₀ : D.CapGraphEndpoint P region chart caps e R₀ G₀ terminal trim)
  (E₁ : D.CapGraphEndpoint P region chart caps e R₁ G₁ terminal trim)

theorem sector_ne_of_region_ne (hR : R₀ ≠ R₁) : E₀.sector ≠ E₁.sector := by
  intro h
  exact hR (E₀.sector_region.symm.trans ((congrArg (region _) h).trans E₁.sector_region))



theorem horizontal_tip_incidence (he : E₀.radialEdge = 2) :
    E₁.radialEdge = 2 ∧ E₁.sector.1 = E₀.sector.1 := by
  have hpoint := E₀.tip_eq_firstOuterTip he
  have hmem := E₁.tip_mem_cap
  rw [hpoint] at hmem
  have hs := ((caps _).firstOuterTip_mem_carrier_iff E₀.sector.1 E₁.sector).mp hmem
  refine ⟨?_, hs⟩
  apply (caps _).radial_tip_injective E₁.sector E₁.radialEdge_valid (Or.inr rfl)
  have hb : (((caps (D.edgeEndpoint e terminal)).face E₁.sector).boundary 2).map 1 =
      (caps (D.edgeEndpoint e terminal)).firstOuterTip E₁.sector.1 := by
    rw [(caps _).boundary_map]
    simpa [affineChartSegment, Fin.succAbove, Fin.lt_def] using
      (caps _).coordinate_first_outer_tip E₁.sector.1 E₁.sector.2
  exact E₁.radial_end.trans (hpoint.trans (by simpa only [hs] using hb.symm))



theorem vertical_tip_incidence (he : E₀.radialEdge = 1) :
    E₁.radialEdge = 1 ∧ E₁.sector.2 = E₀.sector.2 := by
  have hpoint := E₀.tip_eq_secondOuterTip he
  have hmem := E₁.tip_mem_cap
  rw [hpoint] at hmem
  have hs := ((caps _).secondOuterTip_mem_carrier_iff E₀.sector.2 E₁.sector).mp hmem
  refine ⟨?_, hs⟩
  apply (caps _).radial_tip_injective E₁.sector E₁.radialEdge_valid (Or.inl rfl)
  have hb : (((caps (D.edgeEndpoint e terminal)).face E₁.sector).boundary 1).map 1 =
      (caps (D.edgeEndpoint e terminal)).secondOuterTip E₁.sector.2 := by
    rw [(caps _).boundary_map]
    simpa [affineChartSegment] using
      (caps _).coordinate_second_outer_tip E₁.sector.2 E₁.sector.1
  exact E₁.radial_end.trans (hpoint.trans (by simpa only [hs] using hb.symm))

private theorem sum_bool_eq_pair (f : Bool → ℝ) {i j : Bool} (hij : i ≠ j) :
    (∑ k : Bool, f k) = f i + f j := by
  cases i <;> cases j <;> simp_all [add_comm]



theorem sum_refined_caps_add_endpoint_angles (g : RiemannianMetric 2 S)
    (hR : R₀ ≠ R₁) (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g ((caps (D.edgeEndpoint e terminal)).coordinates (j, k))
        ((TriangleMesh.single (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos)
          (rightTriangleBasis (caps (D.edgeEndpoint e terminal)).scale_pos).ind).refineByLines
            (lines (j, k))) (D.edgeFromEndpoint e terminal trim)) +
      g.cornerAngle (D.edgeFromEndpoint e terminal trim) E₀.outwardRadialVelocity E₀.chordVelocity +
      g.cornerAngle (D.edgeFromEndpoint e terminal trim) E₁.outwardRadialVelocity E₁.chordVelocity =
        2 * Real.pi := by
  have hne := E₀.sector_ne_of_region_ne E₁ hR
  rcases E₀.radialEdge_valid with he | he
  · obtain ⟨he₁, hs⟩ := E₀.vertical_tip_incidence E₁ he
    have hi : E₀.sector.1 ≠ E₁.sector.1 := by
      intro h
      exact hne (Prod.ext h hs.symm)
    have hf := (caps (D.edgeEndpoint e terminal)).sum_refined_second_outer_fan g E₀.sector.2 lines
    rw [sum_bool_eq_pair (fun j => g.cornerAngle
      ((caps (D.edgeEndpoint e terminal)).secondOuterTip E₀.sector.2)
      ((caps (D.edgeEndpoint e terminal)).secondOuterSpoke E₀.sector.2)
      ((caps (D.edgeEndpoint e terminal)).secondOuterChord E₀.sector.2 j)) hi,
      ← add_assoc] at hf
    rw [E₀.tip_eq_secondOuterTip he,
      E₀.outwardRadialVelocity_eq_secondOuterSpoke he,
      E₀.chordVelocity_eq_secondOuterChord he,
      E₁.outwardRadialVelocity_eq_secondOuterSpoke he₁,
      E₁.chordVelocity_eq_secondOuterChord he₁, hs]
    exact hf
  · obtain ⟨he₁, hs⟩ := E₀.horizontal_tip_incidence E₁ he
    have hi : E₀.sector.2 ≠ E₁.sector.2 := by
      intro h
      exact hne (Prod.ext hs.symm h)
    have hf := (caps (D.edgeEndpoint e terminal)).sum_refined_first_outer_fan g E₀.sector.1 lines
    rw [sum_bool_eq_pair (fun j => g.cornerAngle
      ((caps (D.edgeEndpoint e terminal)).firstOuterTip E₀.sector.1)
      ((caps (D.edgeEndpoint e terminal)).firstOuterSpoke E₀.sector.1)
      ((caps (D.edgeEndpoint e terminal)).firstOuterChord E₀.sector.1 j)) hi,
      ← add_assoc] at hf
    rw [E₀.tip_eq_firstOuterTip he,
      E₀.outwardRadialVelocity_eq_firstOuterSpoke he,
      E₀.chordVelocity_eq_firstOuterChord he,
      E₁.outwardRadialVelocity_eq_firstOuterSpoke he₁,
      E₁.chordVelocity_eq_firstOuterChord he₁, hs]
    exact hf

end CapGraphEndpoint

section IncidentBands

variable {e : D.EdgeIndex} {cut : D.EdgeIndex → Bool → ℝ}
  (Q : ∀ side : Bool, D.OrientedEdgeGraphSubdivision e
    (if side then D.regionLeft e else D.regionRight e)
    (chartAt (EuclideanSpace ℝ (Fin 2))
      (chart (if side then D.regionLeft e else D.regionRight e))).symm
    (cut e false) (1 - cut e true))
  (L : ∀ side : Bool, D.CapGraphEndpoint P region chart caps e
    (if side then D.regionLeft e else D.regionRight e)
    ((Q side).piece (Q side).firstPiece) false (cut e false))
  (T : ∀ side : Bool, D.CapGraphEndpoint P region chart caps e
    (if side then D.regionLeft e else D.regionRight e)
    ((Q side).piece (Q side).lastPiece) true (cut e true))
  (K : ∀ side : Bool, (Q side).CutChain (L side).direction (T side).direction)
  {r δ : ℝ}



theorem first_cap_tip_refined_fan (g : RiemannianMetric 2 S)
    (B : ∀ side : Bool, ((Q side).piece (Q side).firstPiece).FixedStripBandFaces
      ((K side).graphCuts (Q side).firstPiece) δ r r)
    (hr : r ≤ 1) (capLines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ))
    (bandLines : ∀ side : Bool, (Fin (B side).faces.interface.count × Bool) →
      List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g ((caps (D.edgeEndpoint e false)).coordinates (j, k))
        ((TriangleMesh.single (rightTriangleBasis (caps (D.edgeEndpoint e false)).scale_pos)
          (rightTriangleBasis (caps (D.edgeEndpoint e false)).scale_pos).ind).refineByLines
            (capLines (j, k))) (D.edgeFromEndpoint e false (cut e false))) +
      (∑ side : Bool, ∑ p : Fin (B side).faces.interface.count × Bool,
        meshVertexAngleContribution g ((B side).faces.faceCoordinates p)
          ((TriangleMesh.single ((B side).faces.faceBasis p)
            ((B side).faces.faceBasis p).ind).refineByLines (bandLines side p))
          (D.edgeFromEndpoint e false (cut e false))) = 2 * Real.pi := by
  have hfan := (L true).sum_refined_caps_add_endpoint_angles (L false) g
    (D.region_sides_distinct e) capLines
  simp_rw [(K _).first_cap_band_refined_contribution (L _) (T _) g _ hr]
  have hsum : (∑ side : Bool, g.cornerAngle (D.edgeFromEndpoint e false (cut e false))
      (L side).outwardRadialVelocity (L side).chordVelocity) =
      g.cornerAngle (D.edgeFromEndpoint e false (cut e false))
          (L true).outwardRadialVelocity (L true).chordVelocity +
        g.cornerAngle (D.edgeFromEndpoint e false (cut e false))
          (L false).outwardRadialVelocity (L false).chordVelocity := by simp
  rw [hsum]
  simpa only [add_assoc] using hfan



theorem last_cap_tip_refined_fan (g : RiemannianMetric 2 S)
    (B : ∀ side : Bool, ((Q side).piece (Q side).lastPiece).FixedStripBandFaces
      ((K side).graphCuts (Q side).lastPiece) δ r r)
    (hr : r ≤ 1) (capLines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ))
    (bandLines : ∀ side : Bool, (Fin (B side).faces.interface.count × Bool) →
      List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g ((caps (D.edgeEndpoint e true)).coordinates (j, k))
        ((TriangleMesh.single (rightTriangleBasis (caps (D.edgeEndpoint e true)).scale_pos)
          (rightTriangleBasis (caps (D.edgeEndpoint e true)).scale_pos).ind).refineByLines
            (capLines (j, k))) (D.edgeFromEndpoint e true (cut e true))) +
      (∑ side : Bool, ∑ p : Fin (B side).faces.interface.count × Bool,
        meshVertexAngleContribution g ((B side).faces.faceCoordinates p)
          ((TriangleMesh.single ((B side).faces.faceBasis p)
            ((B side).faces.faceBasis p).ind).refineByLines (bandLines side p))
          (D.edgeFromEndpoint e true (cut e true))) = 2 * Real.pi := by
  have hfan := (T true).sum_refined_caps_add_endpoint_angles (T false) g
    (D.region_sides_distinct e) capLines
  simp_rw [(K _).last_cap_band_refined_contribution (L _) (T _) g _ hr]
  have hsum : (∑ side : Bool, g.cornerAngle (D.edgeFromEndpoint e true (cut e true))
      (T side).outwardRadialVelocity (T side).chordVelocity) =
      g.cornerAngle (D.edgeFromEndpoint e true (cut e true))
          (T true).outwardRadialVelocity (T true).chordVelocity +
        g.cornerAngle (D.edgeFromEndpoint e true (cut e true))
          (T false).outwardRadialVelocity (T false).chordVelocity := by simp
  rw [hsum]
  simpa only [add_assoc] using hfan

end IncidentBands
end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition
