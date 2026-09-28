import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.Graphs.Strips
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.ObliqueFrontier
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Restrictions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition.OrientedGraphPiece

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {D : FiniteChartRegionDecomposition (M := M)} {e : D.EdgeIndex} {R : D.regions}
  {C : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M} {a b : ℝ}
  (G : D.OrientedGraphPiece e R C a b)
  {ua wa ub wb : ℝ}
  (P : TransverseGraphCuts G.lower (G.parameter a) (G.parameter b) ua wa ub wb)

structure FixedStripBandFaces (δ ra rb : ℝ) where
  faces : ObliqueBandFaces (linearGraphCoordinates C G.frame) G.lower
    (G.parameter a) (G.parameter b) ua wa ub wb ra rb
  cuts_left : faces.cuts.left = P.left
  cuts_right : faces.cuts.right = P.right
  radius_le : faces.cuts.radius ≤ δ
  coordinates_eq : ∀ q : ℝ × ℝ,
    faces.coordinates (collarParameterEquiv.symm q) = G.strip P q
  source_subset : ∀ q ∈ faces.coordinates.source,
    collarParameterEquiv q ∈ (G.strip P).source

namespace FixedStripBandFaces

variable {G P} {δ ra rb : ℝ} (B : G.FixedStripBandFaces P δ ra rb)

omit [T2Space M] in
theorem height_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < B.faces.height t ∧ B.faces.height t < δ := by
  refine ⟨B.faces.height_pos ht, ?_⟩
  rw [← B.faces.cut_interval_cover] at ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  rw [B.faces.height_eq_upperGraph hi]
  exact ((B.faces.interface.pieceCoordinates B.faces.open_domain
    B.faces.smooth_lower i).upperGraph_bounds hi).2.trans_le B.radius_le

omit [T2Space M] in
theorem height_zero : B.faces.height 0 = P.left.parameter ra := by
  rw [B.faces.height_zero, B.cuts_left]

omit [T2Space M] in
theorem height_one : B.faces.height 1 = P.right.parameter rb := by
  rw [B.faces.height_one, B.cuts_right]

include B in
omit [T2Space M] in
theorem left_parameter_mem : ra ∈ P.left.parameter.source := by
  rw [← B.cuts_left]
  exact B.faces.interface.left_parameter_mem

include B in
omit [T2Space M] in
theorem right_parameter_mem : rb ∈ P.right.parameter.source := by
  rw [← B.cuts_right]
  exact B.faces.interface.right_parameter_mem

omit [T2Space M] in
theorem subgraph_subset_source :
    {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ B.faces.height q.1} ⊆
      (G.strip P).source := by
  intro q hq
  have hband : collarParameterEquiv.symm q ∈ B.faces.band := by
    rw [B.faces.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply] using hq
  simpa only [collarParameterEquiv.apply_symm_apply] using
    B.source_subset _ (B.faces.band_subset_source hband)

omit [T2Space M] in

theorem carrier_eq_fixed_strip : B.faces.carrier =
    G.strip P '' {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ B.faces.height q.1} := by
  rw [B.faces.carrier_eq_image]
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [B.faces.band_eq_subgraph] at hq
    refine ⟨collarParameterEquiv q, hq, ?_⟩
    simpa only [collarParameterEquiv.symm_apply_apply] using
      (B.coordinates_eq (collarParameterEquiv q)).symm
  · rintro ⟨q, hq, rfl⟩
    refine ⟨collarParameterEquiv.symm q, ?_, B.coordinates_eq q⟩
    rw [B.faces.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply] using hq

omit [T2Space M] in
theorem carrier_subset_strip :
    B.faces.carrier ⊆ G.strip P '' (Icc (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) δ) := by
  rw [B.carrier_eq_fixed_strip]
  apply image_mono
  intro q hq
  exact ⟨hq.1, hq.2.1, hq.2.2.trans_lt (B.height_bounds hq.1).2⟩

end FixedStripBandFaces

theorem exists_fixedStripBandFaces
    (hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source)
    (hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target) (hab : a < b)
    {δ : ℝ} (hδ : 0 < δ) (hδP : δ ≤ P.radius)
    (p : M) (hchart : C.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    ∃ ε > 0, ∀ ra ∈ Ioo (0 : ℝ) ε, ∀ rb ∈ Ioo (0 : ℝ) ε,
      Nonempty (G.FixedStripBandFaces P δ ra rb) := by
  classical
  let F := linearGraphCoordinates C G.frame
  have hF := linearGraphCoordinates_contMDiff C G.frame hC hCinv
  let U := G.parameter.target ∩ Ioo G.tubeLeft G.tubeRight
  have hU : IsOpen U := G.parameter.open_target.inter isOpen_Ioo
  have hUG : U ⊆ G.parameter.target := inter_subset_left
  have hloU : ContDiffOn ℝ ∞ G.lower U := G.lower_smooth.mono hUG
  have hIU : Icc (G.parameter a) (G.parameter b) ⊆ U :=
    fun x hx => ⟨G.interval_target hx,
      ⟨G.tube_left_lt.trans_le hx.1, hx.2.trans_lt G.tube_right_lt⟩⟩
  let r := min δ (G.tubeWidth / 2)
  have hr : 0 < r := lt_min hδ (half_pos G.tube_width_pos)
  have hrδ : r ≤ δ := min_le_left _ _
  have hrP : r ≤ P.radius := hrδ.trans hδP
  have hrG : r < G.tubeWidth :=
    (min_le_right _ _).trans_lt (half_lt_self G.tube_width_pos)
  let Q := P.restrictRadius hr hrP
  have hsource : ∀ x ∈ U, ∀ z : ℝ, 0 ≤ z → z < Q.radius →
      collarParameterEquiv.symm (x, G.lower x + z) ∈ F.source := by
    intro x hx z hz hzr
    refine ⟨mem_univ _, ?_⟩
    change G.frame.symm (collarParameterEquiv
      (collarParameterEquiv.symm (x, G.lower x + z))) ∈ C.source
    rw [collarParameterEquiv.apply_symm_apply]
    apply (G.tube x hx.2 z ?_).1
    rw [abs_of_nonneg hz]
    exact hzr.trans hrG
  obtain ⟨ε, hε, hboundary⟩ := exists_obliquePolygonalBoundary Q (G.parameter_lt hab) hU hloU hIU
  refine ⟨ε, hε, fun ra hra rb hrb => ?_⟩
  obtain ⟨interface⟩ := hboundary ra hra rb hrb
  have hFchart : F.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source := by
    rw [linearGraphCoordinates_target]
    exact hchart
  let B := obliqueBandFacesOfInterface F hF.1 hF.2 hU hloU hIU Q hra.1 hrb.1
    interface hsource p hFchart
  refine ⟨{
    faces := B
    cuts_left := rfl
    cuts_right := rfl
    radius_le := hrδ
    coordinates_eq := ?_
    source_subset := ?_
  }⟩
  · intro q
    rw [B.coordinates_pair_apply, linearGraphCoordinates_apply, collarParameterEquiv.apply_symm_apply]
    change C (G.frame.symm (Q.coordinates hU hloU q)) =
      C (G.frame.symm (P.coordinates G.parameter.open_target G.lower_smooth q))
    rw [P.restrictRadius_coordinates_apply hr hrP hU hloU
      G.parameter.open_target G.lower_smooth]
  · intro q hq
    change q ∈ (obliqueSurfaceCoordinates F Q hU hloU).source at hq
    refine ⟨⟨?_, mem_univ _⟩, ?_⟩
    · exact P.restrictRadius_coordinates_source_subset hr hrP hU hloU
        G.parameter.open_target G.lower_smooth hUG hq.1.1.2
    · change G.frame.symm (P.coordinates G.parameter.open_target G.lower_smooth
        (collarParameterEquiv q)) ∈ C.source
      have hs := hq.2.2
      change G.frame.symm (collarParameterEquiv (collarParameterEquiv.symm
        (Q.coordinates hU hloU (collarParameterEquiv q)))) ∈ C.source at hs
      rw [collarParameterEquiv.apply_symm_apply,
        P.restrictRadius_coordinates_apply hr hrP hU hloU
          G.parameter.open_target G.lower_smooth] at hs
      exact hs

end PoincareConjecture.Topology.Surface.FiniteChartRegionDecomposition.OrientedGraphPiece
