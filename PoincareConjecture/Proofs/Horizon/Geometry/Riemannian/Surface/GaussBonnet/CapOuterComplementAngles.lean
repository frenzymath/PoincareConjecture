import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapOuterSectorAngles







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace Plane S] [IsManifold (𝓡 2) ∞ S]

theorem cornerAngle_pair_of_negative_sector_coordinates
    (g : RiemannianMetric 2 S) (x : S) (c : AffineBasis (Fin 3) ℝ Plane)
    (L : Plane →L[ℝ] TangentSpace (𝓡 2) x) (w : Plane)
    (h1 : (c.coord 1).linear w < 0) (h2 : (c.coord 2).linear w < 0)
    (hne : L w ≠ 0) :
    g.cornerAngle x (L w) (L (c 1 - c 0)) +
      g.cornerAngle x (L w) (L (c 2 - c 0)) =
      2 * Real.pi - g.cornerAngle x (L (c 1 - c 0)) (L (c 2 - c 0)) := by
  have hs := cornerAngle_split_of_positive_sector_coordinates g x c L (-w)
    (by simpa only [map_neg] using neg_pos.mpr h1)
    (by simpa only [map_neg] using neg_pos.mpr h2)
    (by simpa only [map_neg, neg_ne_zero] using hne)
  rw [map_neg, g.cornerAngle_neg_left, g.cornerAngle_neg_left] at hs
  linarith

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

variable {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

private theorem first_outer_angles_eq_sector_pair
    (g : RiemannianMetric 2 S) (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.firstOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.secondOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.secondOuterTip true)) :
    let L := mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm (c 0)
    (∑ j : Bool, g.cornerAngle (B.firstOuterTip i) (B.firstOuterSpoke i)
      (B.firstOuterChord i j)) =
      g.cornerAngle (B.firstOuterTip i) (L (B.firstOuterChartSpoke i v)) (L (c 1 - c 0)) +
      g.cornerAngle (B.firstOuterTip i) (L (B.firstOuterChartSpoke i v)) (L (c 2 - c 0)) := by
  dsimp only
  rw [B.first_outer_angles_eq_chart_differentials g i v hchart, hc0, hc1, hc2]
  simp only [Fintype.sum_bool, add_comm]

private theorem second_outer_angles_eq_sector_pair
    (g : RiemannianMetric 2 S) (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.secondOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.firstOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.firstOuterTip true)) :
    let L := mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm (c 0)
    (∑ j : Bool, g.cornerAngle (B.secondOuterTip i) (B.secondOuterSpoke i)
      (B.secondOuterChord i j)) =
      g.cornerAngle (B.secondOuterTip i) (L (B.secondOuterChartSpoke i v)) (L (c 1 - c 0)) +
      g.cornerAngle (B.secondOuterTip i) (L (B.secondOuterChartSpoke i v)) (L (c 2 - c 0)) := by
  dsimp only
  rw [B.second_outer_angles_eq_chart_differentials g i v hchart, hc0, hc1, hc2]
  simp only [Fintype.sum_bool, add_comm]

theorem first_outer_angles_of_positive_spoke
    (g : RiemannianMetric 2 S) (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.firstOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.secondOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.secondOuterTip true))
    (h1 : 0 < (c.coord 1).linear (B.firstOuterChartSpoke i v))
    (h2 : 0 < (c.coord 2).linear (B.firstOuterChartSpoke i v)) :
    let L := mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm (c 0)
    (∑ j : Bool, g.cornerAngle (B.firstOuterTip i) (B.firstOuterSpoke i)
      (B.firstOuterChord i j)) =
      g.cornerAngle (B.firstOuterTip i) (L (c 1 - c 0)) (L (c 2 - c 0)) := by
  dsimp only
  rw [B.first_outer_angles_eq_sector_pair g i v hchart c hc0 hc1 hc2]
  symm
  apply cornerAngle_split_of_positive_sector_coordinates g _ c _ _ h1 h2
  intro hzero
  apply B.firstOuterSpoke_ne_zero i
  have hv : B.firstOuterTip i ∈ (chartAt Plane v).source := by
    simpa only [hchart] using B.firstOuterTip_mem_chart_source i true
  let A : Plane → Plane := fun z =>
    (mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm z : Plane →L[ℝ] Plane)
      (B.firstOuterChartSpoke i v)
  exact (B.firstOuterSpoke_eq_chart_differential i v hv).trans
    ((congrArg A hc0).symm.trans hzero)

theorem first_outer_angles_of_negative_spoke
    (g : RiemannianMetric 2 S) (i : Bool) (v : S) (hchart : ∀ j, x (i, j) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.firstOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.secondOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.secondOuterTip true))
    (h1 : (c.coord 1).linear (B.firstOuterChartSpoke i v) < 0)
    (h2 : (c.coord 2).linear (B.firstOuterChartSpoke i v) < 0) :
    let L := mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm (c 0)
    (∑ j : Bool, g.cornerAngle (B.firstOuterTip i) (B.firstOuterSpoke i)
      (B.firstOuterChord i j)) =
      2 * Real.pi - g.cornerAngle (B.firstOuterTip i) (L (c 1 - c 0)) (L (c 2 - c 0)) := by
  dsimp only
  rw [B.first_outer_angles_eq_sector_pair g i v hchart c hc0 hc1 hc2]
  apply cornerAngle_pair_of_negative_sector_coordinates g _ c _ _ h1 h2
  intro hzero
  apply B.firstOuterSpoke_ne_zero i
  have hv : B.firstOuterTip i ∈ (chartAt Plane v).source := by
    simpa only [hchart] using B.firstOuterTip_mem_chart_source i true
  let A : Plane → Plane := fun z =>
    (mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm z : Plane →L[ℝ] Plane)
      (B.firstOuterChartSpoke i v)
  exact (B.firstOuterSpoke_eq_chart_differential i v hv).trans
    ((congrArg A hc0).symm.trans hzero)

theorem second_outer_angles_of_positive_spoke
    (g : RiemannianMetric 2 S) (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.secondOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.firstOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.firstOuterTip true))
    (h1 : 0 < (c.coord 1).linear (B.secondOuterChartSpoke i v))
    (h2 : 0 < (c.coord 2).linear (B.secondOuterChartSpoke i v)) :
    let L := mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm (c 0)
    (∑ j : Bool, g.cornerAngle (B.secondOuterTip i) (B.secondOuterSpoke i)
      (B.secondOuterChord i j)) =
      g.cornerAngle (B.secondOuterTip i) (L (c 1 - c 0)) (L (c 2 - c 0)) := by
  dsimp only
  rw [B.second_outer_angles_eq_sector_pair g i v hchart c hc0 hc1 hc2]
  symm
  apply cornerAngle_split_of_positive_sector_coordinates g _ c _ _ h1 h2
  intro hzero
  apply B.secondOuterSpoke_ne_zero i
  have hv : B.secondOuterTip i ∈ (chartAt Plane v).source := by
    simpa only [hchart] using B.secondOuterTip_mem_chart_source i true
  let A : Plane → Plane := fun z =>
    (mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm z : Plane →L[ℝ] Plane)
      (B.secondOuterChartSpoke i v)
  exact (B.secondOuterSpoke_eq_chart_differential i v hv).trans
    ((congrArg A hc0).symm.trans hzero)

theorem second_outer_angles_of_negative_spoke
    (g : RiemannianMetric 2 S) (i : Bool) (v : S) (hchart : ∀ j, x (j, i) = v)
    (c : AffineBasis (Fin 3) ℝ Plane)
    (hc0 : c 0 = chartAt Plane v (B.secondOuterTip i))
    (hc1 : c 1 = chartAt Plane v (B.firstOuterTip false))
    (hc2 : c 2 = chartAt Plane v (B.firstOuterTip true))
    (h1 : (c.coord 1).linear (B.secondOuterChartSpoke i v) < 0)
    (h2 : (c.coord 2).linear (B.secondOuterChartSpoke i v) < 0) :
    let L := mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm (c 0)
    (∑ j : Bool, g.cornerAngle (B.secondOuterTip i) (B.secondOuterSpoke i)
      (B.secondOuterChord i j)) =
      2 * Real.pi - g.cornerAngle (B.secondOuterTip i) (L (c 1 - c 0)) (L (c 2 - c 0)) := by
  dsimp only
  rw [B.second_outer_angles_eq_sector_pair g i v hchart c hc0 hc1 hc2]
  apply cornerAngle_pair_of_negative_sector_coordinates g _ c _ _ h1 h2
  intro hzero
  apply B.secondOuterSpoke_ne_zero i
  have hv : B.secondOuterTip i ∈ (chartAt Plane v).source := by
    simpa only [hchart] using B.secondOuterTip_mem_chart_source i true
  let A : Plane → Plane := fun z =>
    (mfderiv (𝓡 2) (𝓡 2) (chartAt Plane v).symm z : Plane →L[ℝ] Plane)
      (B.secondOuterChartSpoke i v)
  exact (B.secondOuterSpoke_eq_chart_differential i v hv).trans
    ((congrArg A hc0).symm.trans hzero)

end ChartCircleArrangementVertexPatch.VertexCapFaces
end PoincareConjecture.Topology.Surface
