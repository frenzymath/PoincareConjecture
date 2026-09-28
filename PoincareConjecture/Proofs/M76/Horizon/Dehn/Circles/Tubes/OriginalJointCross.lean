import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SignedJointCross

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

open Classical in

theorem ComponentBranchModel.exists_signed_joint_cross
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i) (hcore : D.core ⊆ interior R)
    (s : Finset (D.sample → ℝ × V3)) (hs : s ∈ D.axis.faces) (hcard : s.card = 2)
    (p : D.sample → ℝ × V3) (hps : p ∈ s) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (x y : V2) (C : RawCrossingChart e f R x y) (J : SignedJointCross (D.sample → ℝ × V3)),
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)) ∧
      (∀ z ∈ (D.complex.closedStar p).space,
        z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
          C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0) ∧
      J.disk = (D.complex.barycentricDualBlock s).space ∧
      J.rim = ((D.complex.barycentricDualBlock s).link (s.centroid ℝ id)).space ∧
      J.coordinate = (fun j z => C.chart (D.inverse z) j.castSucc) ∧
      J.center = s.centroid ℝ id ∧
      ∀ j b, ∃ t : Finset (D.sample → ℝ × V3),
        t ∈ ((D.complex.closedStar p).vertexSubcomplex
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}).faces ∧
        s ⊆ t ∧ t.card = 3 ∧ J.endpoint j b = t.centroid ℝ id := by
  classical
  let : Fintype D.complex.faces := D.complex_finite.fintype
  obtain ⟨x, y, C, hC, hface, haxis, hsheet, hJ, hJA, hinterval⟩ :=
    D.exists_raw_edge_joint_intervals hcore s hs hcard p hps
  let K := D.complex.barycentricDualBlock s
  let N (j : Fin 2) := (D.complex.closedStar p).vertexSubcomplex
    {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}
  let _ (j : Fin 2) : Fintype (N j).faces :=
    ((D.complex.closedStar p).vertexSubcomplex_finite _
      (SimplicialComplex.finite_closedStar_faces D.complex_finite p)).fintype
  choose t ht u hu hst hsu htc huc htu hco hI hmI hbI hzero hboundary hneg hpos hradii hmeet
    using hinterval
  let endpoint (j : Fin 2) (b : Bool) := if b then (u j).centroid ℝ id else (t j).centroid ℝ id
  have hKstar : K.space ⊆ (D.complex.closedStar p).space := by
    intro z hz
    have hzV := SimplicialComplex.space_subset_of_le
      (D.complex.barycentricDualBlock_antitone (Finset.singleton_subset_iff.mpr hps)) hz
    obtain ⟨v, hv, hzv⟩ := SimplicialComplex.mem_space_iff.mp hzV
    obtain ⟨w, hw, hvw⟩ := D.complex.exists_original_star_face_of_vertex_dual_face
      (D.axis_le (D.axis.face_subset_vertices hs hps)) hv
    exact (D.complex.closedStar p).convexHull_subset_space hw (hvw hzv)
  have hKK : K.space ⊆ D.complex.space := hKstar.trans
    (SimplicialComplex.space_subset_of_le (show D.complex.closedStar p ≤ D.complex
      from fun _ ht => ht.1))
  let lam (j : Fin 2) (z : D.sample → ℝ × V3) := C.chart (D.inverse z) j.castSucc
  have hcont (j : Fin 2) : ContinuousOn (lam j) K.space :=
    (continuous_apply j.castSucc).comp_continuousOn
      (C.chart.continuousOn.comp (D.inverse_PL.continuousOn.mono hKK)
        (fun _ hz => hC (hKstar hz)))
  have hball (j : Fin 2) : IsFinitePLBallPair ℝ (K.space ∩ {z | lam j z = 0})
      {endpoint j false, endpoint j true} := by
    rw [← hzero j]
    exact hI j
  have hmid (j : Fin 2) : s.centroid ℝ id ∈ (K.space ∩ {z | lam j z = 0}) \
      {endpoint j false, endpoint j true} := by
    rw [← hzero j]
    exact hmI j
  have hrim (j : Fin 2) : (K.link (s.centroid ℝ id)).space ∩ {z | lam j z = 0} =
      {endpoint j false, endpoint j true} := by
    change (K.link (s.centroid ℝ id)).space ∩ {z | lam j z = 0} =
      {(t j).centroid ℝ id, (u j).centroid ℝ id}
    rw [← hboundary j, hzero j]
    ext z
    exact ⟨fun hz => ⟨⟨hJ.1 hz.1, hz.2⟩, hz.1⟩, fun hz => ⟨hz.2, hz.1.2⟩⟩
  have hcross : (K.space ∩ {z | lam 0 z = 0}) ∩
      (K.space ∩ {z | lam 1 z = 0}) = {s.centroid ℝ id} := by
    rw [← hJA]
    ext z
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h0.1, (haxis z (hKstar h0.1)).mpr
        ⟨interior_subset (hcore (D.inverse z).property), h0.2, h1.2⟩⟩
    · rintro ⟨hz, hzA⟩
      have h := (haxis z (hKstar hz)).mp hzA
      exact ⟨⟨hz, h.2.1⟩, hz, h.2.2⟩
  let J : SignedJointCross (D.sample → ℝ × V3) := {
    disk := K.space
    rim := (K.link (s.centroid ℝ id)).space
    coordinate := lam
    center := s.centroid ℝ id
    endpoint := endpoint
    disk_ball := hJ
    coordinate_continuous := hcont
    axis_ball := hball
    center_interior := hmid
    rim_zero := hrim
    axes_intersection := hcross
    endpoint_sign := by intro j b; cases b; exact hneg j; exact hpos j
    axis_radii := by intro j; rw [← hzero j]; exact hradii j }
  refine ⟨x, y, C, J, hC, hface, haxis, rfl, rfl, rfl, rfl, ?_⟩
  intro j b
  cases b
  · exact ⟨t j, ht j, hst j, htc j, rfl⟩
  · exact ⟨u j, hu j, hsu j, huc j, rfl⟩

end PoincareConjecture.M76.Dehn
