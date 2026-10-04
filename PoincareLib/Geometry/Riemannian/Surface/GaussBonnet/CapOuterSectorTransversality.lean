import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.CapOuterSectorAngles
import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.Refinement.SectorTransversality

/-!
# Actual cap-spoke transversality in the common chart

The composed cap and regional-chart differential is injective. It sends
the two original triangle directions to the inward spoke and the actual
straight chord, so neither sector coordinate of the outward spoke vanishes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareMT.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

/-- The actual horizontal cap-chart differential retains the inward
spoke and the outgoing chord and is injective. -/
theorem first_outer_injective_chart_differential
    (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v) (j : Bool) :
    ∃ L : Plane →L[ℝ] Plane, Function.Injective L ∧
      L (rightTriangleBasis B.scale_pos 0 - rightTriangleBasis B.scale_pos 1) =
        -B.firstOuterChartSpoke i v ∧
      L (rightTriangleBasis B.scale_pos 2 - rightTriangleBasis B.scale_pos 1) =
        chartAt Plane v (B.secondOuterTip j) - chartAt Plane v (B.firstOuterTip i) := by
  let F := B.coordinates (i, j)
  let C := chartAt Plane v
  let b := rightTriangleBasis B.scale_pos
  let L : Plane →L[ℝ] Plane := (mfderiv (𝓡 2) (𝓡 2) C (F (b 1))).comp
    (mfderiv (𝓡 2) (𝓡 2) F (b 1))
  have hb : b 1 ∈ F.source :=
    B.triangle_subset_source _ (subset_convexHull ℝ _ (mem_range_self 1))
  have htip : F (b 1) = B.firstOuterTip i := B.coordinate_first_outer_tip i j
  have hc : B.firstOuterTip i ∈ C.source := by
    simpa only [hchart, C] using B.firstOuterTip_mem_chart_source i j
  have hF : F.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨(B.coordinates_smooth _).mdifferentiableOn (by simp),
      (B.coordinates_smooth_symm _).mdifferentiableOn (by simp)⟩
  refine ⟨L, ?_, ?_, ?_⟩
  · exact ((mdifferentiable_chart (I := 𝓡 2) v).mfderiv_injective
      (htip.symm ▸ hc)).comp (hF.mfderiv_injective hb)
  · let D : S → (Plane →L[ℝ] Plane) := fun q => mfderiv (𝓡 2) (𝓡 2) C q
    have hpoint := congrArg D htip
    change D (F (b 1)) ((mfderiv (𝓡 2) (𝓡 2) F (b 1)) (b 0 - b 1)) = _
    rw [← coordinateTriangleVelocity_eq_differential F b (B.coordinates_smooth _)
        (B.triangle_subset_source _), hpoint, B.first_outer_inward_velocity_eq]
    simp only [firstOuterChartSpoke, firstOuterSpoke, map_neg, neg_neg, C, D]
    rfl
  · let D : S → (Plane →L[ℝ] Plane) := fun q => mfderiv (𝓡 2) (𝓡 2) C q
    have hpoint := congrArg D htip
    change D (F (b 1)) ((mfderiv (𝓡 2) (𝓡 2) F (b 1)) (b 2 - b 1)) = _
    rw [← coordinateTriangleVelocity_eq_differential F b (B.coordinates_smooth _)
        (B.triangle_subset_source _), hpoint]
    change (mfderiv (𝓡 2) (𝓡 2) C (B.firstOuterTip i)) (B.firstOuterChord i j) = _
    rw [B.firstOuterChord_eq_common_chart_differential i v hchart j]
    have he := congrArg (fun M : Plane →L[ℝ] Plane =>
      M (C (B.secondOuterTip j) - C (B.firstOuterTip i)))
      ((mdifferentiable_chart (I := 𝓡 2) v).comp_symm_deriv (C.map_source hc))
    change D (C.symm (C (B.firstOuterTip i)))
      ((mfderiv (𝓡 2) (𝓡 2) C.symm (C (B.firstOuterTip i)))
        (C (B.secondOuterTip j) - C (B.firstOuterTip i))) = _ at he
    rw [congrArg D (C.left_inv hc)] at he
    exact he

/-- The vertical cap-chart differential similarly retains its two
actual triangle directions and is injective. -/
theorem second_outer_injective_chart_differential
    (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v) (j : Bool) :
    ∃ L : Plane →L[ℝ] Plane, Function.Injective L ∧
      L (rightTriangleBasis B.scale_pos 0 - rightTriangleBasis B.scale_pos 2) =
        -B.secondOuterChartSpoke i v ∧
      L (rightTriangleBasis B.scale_pos 1 - rightTriangleBasis B.scale_pos 2) =
        chartAt Plane v (B.firstOuterTip j) - chartAt Plane v (B.secondOuterTip i) := by
  let F := B.coordinates (j, i)
  let C := chartAt Plane v
  let b := rightTriangleBasis B.scale_pos
  let L : Plane →L[ℝ] Plane := (mfderiv (𝓡 2) (𝓡 2) C (F (b 2))).comp
    (mfderiv (𝓡 2) (𝓡 2) F (b 2))
  have hb : b 2 ∈ F.source :=
    B.triangle_subset_source _ (subset_convexHull ℝ _ (mem_range_self 2))
  have htip : F (b 2) = B.secondOuterTip i := B.coordinate_second_outer_tip i j
  have hc : B.secondOuterTip i ∈ C.source := by
    simpa only [hchart, C] using B.secondOuterTip_mem_chart_source i j
  have hF : F.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨(B.coordinates_smooth _).mdifferentiableOn (by simp),
      (B.coordinates_smooth_symm _).mdifferentiableOn (by simp)⟩
  refine ⟨L, ?_, ?_, ?_⟩
  · exact ((mdifferentiable_chart (I := 𝓡 2) v).mfderiv_injective
      (htip.symm ▸ hc)).comp (hF.mfderiv_injective hb)
  · let D : S → (Plane →L[ℝ] Plane) := fun q => mfderiv (𝓡 2) (𝓡 2) C q
    have hpoint := congrArg D htip
    change D (F (b 2)) ((mfderiv (𝓡 2) (𝓡 2) F (b 2)) (b 0 - b 2)) = _
    rw [← coordinateTriangleVelocity_eq_differential F b (B.coordinates_smooth _)
        (B.triangle_subset_source _), hpoint, B.second_outer_inward_velocity_eq]
    simp only [secondOuterChartSpoke, secondOuterSpoke, map_neg, neg_neg, C, D]
    rfl
  · let D : S → (Plane →L[ℝ] Plane) := fun q => mfderiv (𝓡 2) (𝓡 2) C q
    have hpoint := congrArg D htip
    change D (F (b 2)) ((mfderiv (𝓡 2) (𝓡 2) F (b 2)) (b 1 - b 2)) = _
    rw [← coordinateTriangleVelocity_eq_differential F b (B.coordinates_smooth _)
        (B.triangle_subset_source _), hpoint]
    change (mfderiv (𝓡 2) (𝓡 2) C (B.secondOuterTip i)) (B.secondOuterChord i j) = _
    rw [B.secondOuterChord_eq_common_chart_differential i v hchart j]
    have he := congrArg (fun M : Plane →L[ℝ] Plane =>
      M (C (B.firstOuterTip j) - C (B.secondOuterTip i)))
      ((mdifferentiable_chart (I := 𝓡 2) v).comp_symm_deriv (C.map_source hc))
    change D (C.symm (C (B.secondOuterTip i)))
      ((mfderiv (𝓡 2) (𝓡 2) C.symm (C (B.secondOuterTip i)))
        (C (B.firstOuterTip j) - C (B.secondOuterTip i))) = _ at he
    rw [congrArg D (C.left_inv hc)] at he
    exact he

/-- Neither coordinate of the actual horizontal outward spoke vanishes
in the basis determined by the two actual outgoing chords. -/
theorem firstOuterChartSpoke_coordinates_ne_zero
    (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.firstOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.secondOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.secondOuterTip true)) :
    (c.coord 1).linear (B.firstOuterChartSpoke i v) ≠ 0 ∧
      (c.coord 2).linear (B.firstOuterChartSpoke i v) ≠ 0 := by
  obtain ⟨L₁, hL₁, hw₁, hd₁⟩ := B.first_outer_injective_chart_differential i v hchart false
  obtain ⟨L₂, hL₂, hw₂, hd₂⟩ := B.first_outer_injective_chart_differential i v hchart true
  constructor
  · exact affineBasis_first_coord_ne_zero_of_mapped_second_edge
      (rightTriangleBasis B.scale_pos) c L₂ hL₂ 1 0 2 (by decide) (by decide)
      (B.firstOuterChartSpoke i v) hw₂ (by rwa [hc0, hc2])
  · exact affineBasis_second_coord_ne_zero_of_mapped_first_edge
      (rightTriangleBasis B.scale_pos) c L₁ hL₁ 1 0 2 (by decide) (by decide)
      (B.firstOuterChartSpoke i v) hw₁ (by rwa [hc0, hc1])

/-- The two coordinates of the actual vertical outward spoke are also
nonzero in its actual chord basis. -/
theorem secondOuterChartSpoke_coordinates_ne_zero
    (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.secondOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.firstOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.firstOuterTip true)) :
    (c.coord 1).linear (B.secondOuterChartSpoke i v) ≠ 0 ∧
      (c.coord 2).linear (B.secondOuterChartSpoke i v) ≠ 0 := by
  obtain ⟨L₁, hL₁, hw₁, hd₁⟩ := B.second_outer_injective_chart_differential i v hchart false
  obtain ⟨L₂, hL₂, hw₂, hd₂⟩ := B.second_outer_injective_chart_differential i v hchart true
  constructor
  · exact affineBasis_first_coord_ne_zero_of_mapped_second_edge
      (rightTriangleBasis B.scale_pos) c L₂ hL₂ 2 0 1 (by decide) (by decide)
      (B.secondOuterChartSpoke i v) hw₂ (by rwa [hc0, hc2])
  · exact affineBasis_second_coord_ne_zero_of_mapped_first_edge
      (rightTriangleBasis B.scale_pos) c L₁ hL₁ 2 0 1 (by decide) (by decide)
      (B.secondOuterChartSpoke i v) hw₁ (by rwa [hc0, hc1])

end PoincareMT.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces
