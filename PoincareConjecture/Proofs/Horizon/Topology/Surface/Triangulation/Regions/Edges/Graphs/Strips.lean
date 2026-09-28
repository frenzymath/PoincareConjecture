


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Data
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.LinearCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.DisjointStrips








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition.OrientedGraphPiece

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  (G : D.OrientedGraphPiece e R C a b)

variable {ua wa ub wb : ℝ}
  (P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb)


noncomputable def strip : OpenPartialHomeomorph (ℝ × ℝ) M :=
  (P.linearCoordinates G.frame.symm G.parameter.open_target G.lower_smooth).trans C

omit [T2Space M]

theorem strip_apply (q : ℝ × ℝ) :
    G.strip P q = C (G.frame.symm
      (P.A q.2 + q.1 * (P.B q.2 - P.A q.2),
        G.lower (P.A q.2 + q.1 * (P.B q.2 - P.A q.2)) + q.2)) := by
  change C (P.linearCoordinates G.frame.symm G.parameter.open_target G.lower_smooth q) = _
  rw [P.linearCoordinates_apply, P.coordinates_apply]
  rfl

theorem strip_axis (t : ℝ) :
    G.strip P (t, 0) = C (G.frame.symm
      (G.parameter a + t * (G.parameter b - G.parameter a),
        G.lower (G.parameter a + t * (G.parameter b - G.parameter a)))) := by
  change C (P.linearCoordinates G.frame.symm G.parameter.open_target G.lower_smooth (t, 0)) = _
  rw [P.linearCoordinates_axis]

theorem strip_axis_mem_source (hab : a < b) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t, (0 : ℝ)) ∈ (G.strip P).source := by
  refine ⟨P.linearCoordinates_axis_mem_source G.frame.symm G.parameter.open_target
    G.lower_smooth (G.parameter_lt hab) G.interval_target ht, ?_⟩
  change P.linearCoordinates G.frame.symm G.parameter.open_target G.lower_smooth (t, 0) ∈ C.source
  rw [P.linearCoordinates_axis]
  apply G.graph_source _ (G.interval_target ?_)
  have h := G.parameter_lt hab
  constructor <;> nlinarith [ht.1, ht.2]

theorem strip_axis_image (hab : a < b) :
    (fun t => G.strip P (t, 0)) '' Icc (0 : ℝ) 1 =
      (D.edge e.1 e.2).map '' Icc a b := by
  let f : ℝ → ℝ := fun t => G.parameter a + t * (G.parameter b - G.parameter a)
  have hf : f '' Icc (0 : ℝ) 1 = Icc (G.parameter a) (G.parameter b) := by
    have he : f = AffineMap.lineMap (G.parameter a) (G.parameter b) := by
      funext t
      simp only [f, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      ring
    rw [he, ← segment_eq_image_lineMap, segment_eq_Icc (G.parameter_lt hab).le]
  calc
    _ = (fun x => C (G.frame.symm (x, G.lower x))) '' (f '' Icc (0 : ℝ) 1) := by
      rw [image_image]
      exact image_congr (fun t _ => G.strip_axis P t)
    _ = _ := by rw [hf, G.graph_image]



theorem exists_strip_region_width (hab : a < b) :
    ∃ δ > 0, δ ≤ P.radius ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ z : ℝ, |z| < δ →
        (t, z) ∈ (G.strip P).source ∧
        (G.strip P (t, z) ∈ chartDiskBoundaryUnion D.centers D.radius ↔ z = 0) ∧
        (G.strip P (t, z) ∈ connectedComponentIn
          (chartDiskBoundaryUnion D.centers D.radius)ᶜ R ↔ 0 < z) ∧
        (0 ≤ z → G.strip P (t, z) ∈ closure (connectedComponentIn
          (chartDiskBoundaryUnion D.centers D.radius)ᶜ R)) := by
  have hga := G.parameter_lt hab
  have hA : ContinuousAt P.A 0 := P.smooth_A.continuousOn.continuousAt
    (isOpen_Ioo.mem_nhds ⟨by linarith [P.radius_pos], P.radius_pos⟩)
  have hB : ContinuousAt P.B 0 := P.smooth_B.continuousOn.continuousAt
    (isOpen_Ioo.mem_nhds ⟨by linarith [P.radius_pos], P.radius_pos⟩)
  have hleft : P.A 0 ∈ Ioo G.tubeLeft G.tubeRight := by
    simpa only [P.A_zero, mem_Ioo] using And.intro G.tube_left_lt (hga.trans G.tube_right_lt)
  have hright : P.B 0 ∈ Ioo G.tubeLeft G.tubeRight := by
    simpa only [P.B_zero, mem_Ioo] using And.intro (G.tube_left_lt.trans hga) G.tube_right_lt
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hA.preimage_mem_nhds (isOpen_Ioo.mem_nhds hleft))
      (hB.preimage_mem_nhds (isOpen_Ioo.mem_nhds hright)))
  obtain ⟨s, hs, hsource⟩ := exists_strip_source_width (G.strip P)
    (fun _ ht => G.strip_axis_mem_source P hab ht)
  let δ := min (min r s) (min G.tubeWidth P.radius)
  have hδ : 0 < δ := lt_min (lt_min hr hs) (lt_min G.tube_width_pos P.radius_pos)
  have hδr : δ ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hδs : δ ≤ s := (min_le_left _ _).trans (min_le_right _ _)
  have hδG : δ ≤ G.tubeWidth := (min_le_right _ _).trans (min_le_left _ _)
  have hδP : δ ≤ P.radius := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, hδP, fun t ht z hz => ?_⟩
  have habz := hball (show z ∈ Metric.ball (0 : ℝ) r by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hz.trans_le hδr)
  have hx : P.A z + t * (P.B z - P.A z) ∈ Ioo G.tubeLeft G.tubeRight := by
    have hconv := (convex_Ioo G.tubeLeft G.tubeRight).segment_subset habz.1 habz.2
      (lineMap_mem_segment ℝ (P.A z) (P.B z) ht)
    convert hconv using 1
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  have h := G.tube _ hx z (hz.trans_le hδG)
  exact ⟨hsource ⟨ht, abs_lt.mp (hz.trans_le hδs)⟩, by simpa only [G.strip_apply P] using h.2⟩

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition.OrientedGraphPiece
