import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterSectorAngles







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

theorem first_outer_chart_chord_ne_zero (i : Bool) (v : S)
    (hchart : ∀ j, x (i, j) = v) (j : Bool) :
    chartAt Plane v (B.secondOuterTip j) - chartAt Plane v (B.firstOuterTip i) ≠ 0 := by
  intro hzero
  have h := B.firstOuterChord_eq_common_chart_differential i v hchart j
  rw [hzero, map_zero] at h
  exact coordinateTriangleVelocity_ne_zero (B.coordinates (i, j))
    (rightTriangleBasis B.scale_pos) (B.coordinates_smooth _) (B.coordinates_smooth_symm _)
    (B.triangle_subset_source _) (by decide : (1 : Fin 3) ≠ 2) h

theorem second_outer_chart_chord_ne_zero (i : Bool) (v : S)
    (hchart : ∀ j, x (j, i) = v) (j : Bool) :
    chartAt Plane v (B.firstOuterTip j) - chartAt Plane v (B.secondOuterTip i) ≠ 0 := by
  intro hzero
  have h := B.secondOuterChord_eq_common_chart_differential i v hchart j
  rw [hzero, map_zero] at h
  exact coordinateTriangleVelocity_ne_zero (B.coordinates (j, i))
    (rightTriangleBasis B.scale_pos) (B.coordinates_smooth _) (B.coordinates_smooth_symm _)
    (B.triangle_subset_source _) (by decide : (2 : Fin 3) ≠ 1) h

private theorem cornerAngle_pair_of_negative_smul (g : RiemannianMetric 2 S)
    (q : S) (w d e : TangentSpace (𝓡 2) q) {a : ℝ}
    (ha : a < 0) (he : e = a • d) :
    g.cornerAngle q w d + g.cornerAngle q w e = Real.pi := by
  have he' : e = (-a) • (-d) := by rw [he, smul_neg, neg_smul, neg_neg]
  rw [he', g.cornerAngle_smul_pos_right q w (-d) (neg_pos.mpr ha),
    g.cornerAngle_neg_right]
  ring

variable [T2Space S]

theorem first_outer_angles_eq_pi_of_not_independent
    (g : RiemannianMetric 2 S) (i : Bool) (v : S)
    (hchart : ∀ j, x (i, j) = v)
    (hdep : ¬ LinearIndependent ℝ (![chartAt Plane v (B.secondOuterTip false) -
      chartAt Plane v (B.firstOuterTip i), chartAt Plane v (B.secondOuterTip true) -
      chartAt Plane v (B.firstOuterTip i)] : Fin 2 → Plane)) :
    (∑ j : Bool, g.cornerAngle (B.firstOuterTip i)
      (B.firstOuterSpoke i) (B.firstOuterChord i j)) = Real.pi := by
  obtain hi | ⟨a, ha, he⟩ := independent_or_negative_smul_of_not_pos_smul
    (B.first_outer_chart_chord_ne_zero i v hchart false)
    (B.first_outer_chart_chord_ne_zero i v hchart true)
    (fun a ha => B.first_outer_chords_not_pos_smul i v hchart ha)
  · exact (hdep hi).elim
  have hd : B.firstOuterChord i true = a • B.firstOuterChord i false := by
    rw [B.firstOuterChord_eq_common_chart_differential i v hchart true,
      B.firstOuterChord_eq_common_chart_differential i v hchart false, he, map_smul]
  rw [Fintype.sum_bool, add_comm]
  exact cornerAngle_pair_of_negative_smul g _ _ _ _ ha hd

theorem second_outer_angles_eq_pi_of_not_independent
    (g : RiemannianMetric 2 S) (i : Bool) (v : S)
    (hchart : ∀ j, x (j, i) = v)
    (hdep : ¬ LinearIndependent ℝ (![chartAt Plane v (B.firstOuterTip false) -
      chartAt Plane v (B.secondOuterTip i), chartAt Plane v (B.firstOuterTip true) -
      chartAt Plane v (B.secondOuterTip i)] : Fin 2 → Plane)) :
    (∑ j : Bool, g.cornerAngle (B.secondOuterTip i)
      (B.secondOuterSpoke i) (B.secondOuterChord i j)) = Real.pi := by
  obtain hi | ⟨a, ha, he⟩ := independent_or_negative_smul_of_not_pos_smul
    (B.second_outer_chart_chord_ne_zero i v hchart false)
    (B.second_outer_chart_chord_ne_zero i v hchart true)
    (fun a ha => B.second_outer_chords_not_pos_smul i v hchart ha)
  · exact (hdep hi).elim
  have hd : B.secondOuterChord i true = a • B.secondOuterChord i false := by
    rw [B.secondOuterChord_eq_common_chart_differential i v hchart true,
      B.secondOuterChord_eq_common_chart_differential i v hchart false, he, map_smul]
  rw [Fintype.sum_bool, add_comm]
  exact cornerAngle_pair_of_negative_smul g _ _ _ _ ha hd

theorem sum_refined_first_outer_fan_eq_pi_of_not_independent
    (g : RiemannianMetric 2 S) (i : Bool) (v : S)
    (hchart : ∀ j, x (i, j) = v)
    (hdep : ¬ LinearIndependent ℝ (![chartAt Plane v (B.secondOuterTip false) -
      chartAt Plane v (B.firstOuterTip i), chartAt Plane v (B.secondOuterTip true) -
      chartAt Plane v (B.firstOuterTip i)] : Fin 2 → Plane))
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g (B.coordinates (j, k))
        ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (j, k)))
        (B.firstOuterTip i)) = Real.pi := by
  have h := B.sum_refined_first_outer_fan g i lines
  rw [B.first_outer_angles_eq_pi_of_not_independent g i v hchart hdep] at h
  linarith

theorem sum_refined_second_outer_fan_eq_pi_of_not_independent
    (g : RiemannianMetric 2 S) (i : Bool) (v : S)
    (hchart : ∀ j, x (j, i) = v)
    (hdep : ¬ LinearIndependent ℝ (![chartAt Plane v (B.firstOuterTip false) -
      chartAt Plane v (B.secondOuterTip i), chartAt Plane v (B.firstOuterTip true) -
      chartAt Plane v (B.secondOuterTip i)] : Fin 2 → Plane))
    (lines : Bool × Bool → List (Plane →ᵃ[ℝ] ℝ)) :
    (∑ j : Bool, ∑ k : Bool,
      meshVertexAngleContribution g (B.coordinates (j, k))
        ((TriangleMesh.single (rightTriangleBasis B.scale_pos)
          (rightTriangleBasis B.scale_pos).ind).refineByLines (lines (j, k)))
        (B.secondOuterTip i)) = Real.pi := by
  have h := B.sum_refined_second_outer_fan g i lines
  rw [B.second_outer_angles_eq_pi_of_not_independent g i v hchart hdep] at h
  linarith

end PoincareConjecture.Topology.Surface.ChartCircleArrangementVertexPatch.VertexCapFaces
