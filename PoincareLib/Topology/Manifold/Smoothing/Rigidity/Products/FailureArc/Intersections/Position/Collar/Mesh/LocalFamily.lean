import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.PairMotion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.EdgeCarrier

/-! # Original-atlas local motions chosen after the final common refinement -/

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareMT.M76
local notation "E" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem OriginalSurfacePairChart.exists_local_refinement_motion_family
    {D X ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S T : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K : SimplicialComplex ℝ D) (hK : K.faces.Finite)
    {g : D → X} (hg : PolyhedralPLInCharts e g K.space)
    (himage : MapsTo g K.space (C.chart.trans C.coordinates).source)
    {U : Set X} (hU : IsOpen U) (hyU : y ∈ U) :
    let Q := C.chart.trans C.coordinates
    ∃ (r : ℝ) (J : SimplicialComplex ℝ D) (A W : Set X),
      0 < r ∧ J.faces.Finite ∧ J.IsSubdivision K ∧
      IsCompact A ∧ A ⊆ U ∧ IsOpen W ∧ y ∈ W ∧ W ⊆ U ∧
      A = Q.symm '' closedBall (0 : E) r ∧ W = Q.symm '' ball (0 : E) r ∧
      ∀ (N : SimplicialComplex ℝ D), N.faces.Finite → N.IsSubdivision J →
      ∀ epsilon : ℝ, 0 < epsilon →
      ∃ (c : ℝ) (F : X ≃ₜ X), c ∈ Ioo (0 : ℝ) epsilon ∧
        EqOn F id Aᶜ ∧
        (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        F ⁻¹' T = T ∧
        (∀ z ∈ Q.target, Q.symm z ∈ F '' S ↔
          (CollarMesh.normalGraphCoordinates r c z).2 = 0 ∧ (b = true → 0 ≤ z.1.2)) ∧
        N.AffineOnFaces ((CollarMesh.normalGraphCoordinates r c) ∘ Q ∘ g) ∧
        Disjoint (F '' S) (g '' N.vertices ∩ W) ∧
        ∀ (R : Set X) (B : Set (ℝ × ℝ)),
          (∀ z ∈ C.coordinates.source,
            C.chart.symm z ∈ R ↔ (C.coordinates z).1 ∈ B) → F ⁻¹' R = R := by
  let Q := C.chart.trans C.coordinates
  have hyQ : y ∈ Q.source := ⟨C.center_source, C.center_coordinates⟩
  have hQy : Q y = 0 := C.center_zero
  have hzeroQ : (0 : E) ∈ Q.target := hQy ▸ Q.map_source hyQ
  have hQzero : Q.symm 0 = y := by rw [← hQy, Q.left_inv hyQ]
  let O : Set E := Q.target ∩ Q.symm ⁻¹' U
  have hO : IsOpen O := Q.symm.isOpen_inter_preimage hU
  have hzeroO : (0 : E) ∈ O := ⟨hzeroQ, by change Q.symm 0 ∈ U; rw [hQzero]; exact hyU⟩
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO 0 hzeroO
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hballO : closedBall (0 : E) r ⊆ O := by
    intro z hz
    exact hεO ((mem_closedBall.mp hz).trans_lt (half_lt_self hε))
  have hballQ := hballO.trans inter_subset_left
  have hQPL (i : ι) : LocallyPiecewiseAffineOn ((e i).symm.trans Q)
      ((e i).symm.trans Q).source := by
    have h := ((mem_piecewiseAffineGroupoid_iff V3 _).mp (C.compatible i)).1
    simpa only [Q, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.trans_source, preimage_inter, preimage_comp, inter_assoc,
      Function.comp_assoc] using C.forwardPL.comp h
  have hf := CollarMesh.finitePL_in_mixed_chart K hK hg Q hQPL himage
  obtain ⟨J, hJ, hJK, hfamily⟩ :=
    CollarMesh.exists_normal_graph_source_refinement_family K hK hf r
  let A := Q.symm '' closedBall (0 : E) r
  let W := Q.symm '' ball (0 : E) r
  have hWQ : W ⊆ Q.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact Q.map_target (hballQ (ball_subset_closedBall hz))
  refine ⟨r, J, A, W, hr, hJ, hJK,
    (isCompact_closedBall _ _).image_of_continuousOn (Q.symm.continuousOn.mono hballQ),
    ?_, Q.symm.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hballQ), ⟨0, mem_ball_self hr, hQzero⟩,
    ?_, rfl, rfl, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hballO hz).2
  · rintro _ ⟨z, hz, rfl⟩
    exact (hballO (ball_subset_closedBall hz)).2
  · intro N hN hNJ epsilon hepsilon
    obtain ⟨c, H, hc, hHPL, hval, hoff, _, _, hfaces, hvertices⟩ :=
      hfamily N hN hNJ epsilon hepsilon
    obtain ⟨F, _, hFoff, hFPL, hFinv, hFT, hS, hmarks⟩ :=
      C.exists_supported_normal_motion he H hHPL hval hoff hballQ
    refine ⟨c, F, hc, hFoff, hFPL, hFinv, hFT, hS, ?_, ?_, hmarks⟩
    · simpa only [Function.comp_assoc] using hfaces
    · apply disjoint_left.mpr
      rintro x hxS ⟨⟨v, hv, rfl⟩, hvW⟩
      have hvQ := hWQ hvW
      have hvz := (hS (Q (g v)) (Q.map_source hvQ)).mp
        (by change Q.symm (Q (g v)) ∈ F '' S; rwa [Q.left_inv hvQ])
      have hplane : Q (g v) ∈ H '' {p : E | p.2 = 0} :=
        (CollarMesh.normalGraphCoordinates_surface hval _).mpr hvz.1
      have hnorm : ‖(Q (g v)).1‖ < r := by
        obtain ⟨z, hz, heq⟩ := hvW
        have hzQ := hballQ (ball_subset_closedBall hz)
        rw [← heq, Q.right_inv hzQ]
        exact (norm_fst_le z).trans_lt (mem_ball_zero_iff.mp hz)
      exact disjoint_left.mp hvertices hplane ⟨⟨v, hv, rfl⟩, hnorm⟩

end PoincareMT.M76
