import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterSectorSigns
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterSectorTransversality







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

theorem firstOuterChartSpoke_pos_of_reflex_cap_germ
    (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.firstOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.secondOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.secondOuterTip true))
    (hcap : (chartAt Plane v).symm ⁻¹' (⋃ s, (B.face s).carrier) =ᶠ[𝓝 (c 0)]
      {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) :
    0 < (c.coord 1).linear (B.firstOuterChartSpoke i v) ∧
      0 < (c.coord 2).linear (B.firstOuterChartSpoke i v) := by
  have h := B.firstOuterChartSpoke_nonneg_of_reflex_cap_germ i v hchart c hc0 hc1 hc2 hcap
  have hn := B.firstOuterChartSpoke_coordinates_ne_zero i v hchart c hc0 hc1 hc2
  exact ⟨lt_of_le_of_ne h.1 hn.1.symm, lt_of_le_of_ne h.2 hn.2.symm⟩

theorem secondOuterChartSpoke_pos_of_reflex_cap_germ
    (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.secondOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.firstOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.firstOuterTip true))
    (hcap : (chartAt Plane v).symm ⁻¹' (⋃ s, (B.face s).carrier) =ᶠ[𝓝 (c 0)]
      {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0}) :
    0 < (c.coord 1).linear (B.secondOuterChartSpoke i v) ∧
      0 < (c.coord 2).linear (B.secondOuterChartSpoke i v) := by
  have h := B.secondOuterChartSpoke_nonneg_of_reflex_cap_germ i v hchart c hc0 hc1 hc2 hcap
  have hn := B.secondOuterChartSpoke_coordinates_ne_zero i v hchart c hc0 hc1 hc2
  exact ⟨lt_of_le_of_ne h.1 hn.1.symm, lt_of_le_of_ne h.2 hn.2.symm⟩

theorem firstOuterChartSpoke_neg_of_convex_cap_germ
    (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.firstOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.secondOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.secondOuterTip true))
    (hcap : (chartAt Plane v).symm ⁻¹' (⋃ s, (B.face s).carrier) =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    (c.coord 1).linear (B.firstOuterChartSpoke i v) < 0 ∧
      (c.coord 2).linear (B.firstOuterChartSpoke i v) < 0 := by
  have h := B.firstOuterChartSpoke_nonpos_of_convex_cap_germ i v hchart c hc0 hcap
  have hn := B.firstOuterChartSpoke_coordinates_ne_zero i v hchart c hc0 hc1 hc2
  exact ⟨lt_of_le_of_ne h.1 hn.1, lt_of_le_of_ne h.2 hn.2⟩

theorem secondOuterChartSpoke_neg_of_convex_cap_germ
    (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.secondOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.firstOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.firstOuterTip true))
    (hcap : (chartAt Plane v).symm ⁻¹' (⋃ s, (B.face s).carrier) =ᶠ[𝓝 (c 0)]
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z}) :
    (c.coord 1).linear (B.secondOuterChartSpoke i v) < 0 ∧
      (c.coord 2).linear (B.secondOuterChartSpoke i v) < 0 := by
  have h := B.secondOuterChartSpoke_nonpos_of_convex_cap_germ i v hchart c hc0 hcap
  have hn := B.secondOuterChartSpoke_coordinates_ne_zero i v hchart c hc0 hc1 hc2
  exact ⟨lt_of_le_of_ne h.1 hn.1, lt_of_le_of_ne h.2 hn.2⟩

end PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces
