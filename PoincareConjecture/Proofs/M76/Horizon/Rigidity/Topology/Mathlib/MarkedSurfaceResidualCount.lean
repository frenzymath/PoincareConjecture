import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CountTwoSphere
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleIncidenceRanks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalEdgeComponentConnected










set_option autoImplicit false
open Set PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

private theorem surfaceEulerCount_le_top_kernel
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    [Fintype K.vertices] (hconn : IsConnected K.space) {n : ℕ}
    (hbound : Module.finrank (ZMod 2)
      (LinearMap.ker (edgeCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex).dualMap) ≤ n) :
    K.surfaceEulerCount ≤ 1 + (n : ℤ) := by
  classical
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  change Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A).dualMap) ≤ n at hbound
  have hgraph := K.connected_edgeGraph_of_isConnected hK hconn
  have h0 := (vertexCoboundary A).finrank_range_add_finrank_ker
  rw [K.vertexAbstractComplex.finrank_ker_vertexCoboundary hgraph, Module.finrank_pi] at h0
  have h1 := (vertexCoboundary A).dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq,
    Module.finrank_pi] at h1
  have h2 := (edgeCoboundary A).dualMap.finrank_range_add_finrank_ker
  rw [Subspace.dual_finrank_eq, Module.finrank_pi] at h2
  have hTZ : LinearMap.range (edgeCoboundary A).dualMap ≤
      LinearMap.ker (vertexCoboundary A).dualMap := by
    rintro _ ⟨c, rfl⟩
    apply LinearMap.ext
    intro f
    change c (edgeCoboundary A (vertexCoboundary A f)) = 0
    rw [edgeCoboundary_vertexCoboundary, map_zero]
  have hle := Submodule.finrank_mono hTZ
  rw [K.surfaceEulerCount_eq_vertex_counts]
  change (Nat.card K.vertices : ℤ) - Nat.card (Edge A) + Nat.card (Triangle A) ≤ _
  simp only [Nat.card_eq_fintype_card]
  omega

theorem surfaceEulerCount_le_one_of_boundary_edge
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard ≤ 2)
    (hboundary : ∃ s ∈ K.faces, s.card = 2 ∧
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 1) :
    K.surfaceEulerCount ≤ 1 := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  have htri := K.vertex_triangleGraph_connected
    (K.triangleGraph_connected_of_isConnected hK
      (fun s hs => by
        obtain ⟨t, ht, htc, hst⟩ := hpure s hs
        exact ⟨t, ht, hst, htc⟩)
      hconn (fun v hv => by simpa only [K.faceLink_singleton_eq_link] using hlinks v hv))
  have hle (e : Edge A) : (triangleCofaces A e).card ≤ 2 := by
    rw [K.triangleCofaces_card_eq_original]
    exact hcofaces _ e.property.1 (by simpa only [Finset.card_map] using e.property.2)
  have hone : ∃ e : Edge A, (triangleCofaces A e).card = 1 := by
    obtain ⟨s, hs, hsc, hc⟩ := hboundary
    let eg : Edge K.toPreAbstractSimplicialComplex := ⟨s, hs, hsc⟩
    let ev : Edge A := (K.vertexFaceEquiv 2).symm eg
    refine ⟨ev, ?_⟩
    rw [K.triangleCofaces_card_eq_original]
    change {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧
      ((K.vertexFaceEquiv 2).symm eg).val.map (Function.Embedding.subtype _) ⊆ t}.ncard = 1
    rw [K.vertexFaceEquiv_symm_map]
    exact hc
  have htop := finrank_boundary2_ker_of_one_coface A hle htri.preconnected hone
  simpa using K.surfaceEulerCount_le_top_kernel hK hconn (n := 0) htop.le

theorem exists_residual_count_of_marked_surface
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      let n := {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard
      n = 1 ∨ n = 2) :
    ∃ r : ℕ, K.surfaceEulerCount = 2 - (r : ℤ) ∧
      ((∃ s ∈ K.faces, s.card = 2 ∧
        {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 1) → 0 < r) ∧
      (r = 0 → ∃ H : K.space ≃ₜ frontier (TriangularRoofModel.halfBall 1), H.IsFinitePL) := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let B : Prop := ∃ s ∈ K.faces, s.card = 2 ∧
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 1
  have hone (hB : B) : K.surfaceEulerCount ≤ 1 :=
    K.surfaceEulerCount_le_one_of_boundary_edge hK hpure hconn hlinks
      (fun s hs hsc => by rcases hcofaces s hs hsc with h | h <;> omega) hB
  have htwo (hB : ¬ B) (s : Finset E) (hs : s ∈ K.faces) (hsc : s.card = 2) :
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 :=
    (hcofaces s hs hsc).resolve_left (fun h => hB ⟨s, hs, hsc, h⟩)
  have hcount : K.surfaceEulerCount ≤ 2 := by
    by_cases hB : B
    · exact (hone hB).trans (by norm_num)
    · let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
      have htri := K.vertex_triangleGraph_connected
        (K.triangleGraph_connected_of_isConnected hK
          (fun s hs => by
            obtain ⟨t, ht, htc, hst⟩ := hpure s hs
            exact ⟨t, ht, hst, htc⟩)
          hconn (fun v hv => by simpa only [K.faceLink_singleton_eq_link] using hlinks v hv))
      have htop := finrank_boundary2_ker_of_two_cofaces A (fun e => by
        rw [K.triangleCofaces_card_eq_original]
        exact htwo hB _ e.property.1 (by simpa only [Finset.card_map] using e.property.2)) htri
      simpa using K.surfaceEulerCount_le_top_kernel hK hconn (n := 1) htop.le
  let r := (2 - K.surfaceEulerCount).toNat
  have hr : (r : ℤ) = 2 - K.surfaceEulerCount := Int.toNat_of_nonneg (by omega)
  refine ⟨r, by omega, ?_, ?_⟩
  · intro hB
    have := hone hB
    omega
  · intro hz
    have hc : K.surfaceEulerCount = 2 := by omega
    have hB : ¬ B := by intro h; have := hone h; omega
    exact K.exists_sphere_model_of_surfaceEulerCount_eq_two hK hpure (htwo hB) hlinks hconn hc

theorem exists_component_residual_counts_of_marked_surface
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      let n := {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard
      n = 1 ∨ n = 2) :
    ∃ r : K.vertexAbstractComplex.edgeGraph.ConnectedComponent → ℕ, ∀ C,
      (K.edgeComponentComplex C).surfaceEulerCount = 2 - (r C : ℤ) ∧
      ((∃ s ∈ (K.edgeComponentComplex C).faces, s.card = 2 ∧
        {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 1) → 0 < r C) ∧
      (r C = 0 → ∃ H : (K.edgeComponentComplex C).space ≃ₜ
        frontier (TriangularRoofModel.halfBall 1), H.IsFinitePL) := by
  classical
  have hex (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :=
    (K.edgeComponentComplex C).exists_residual_count_of_marked_surface
      (hK.subset (K.edgeComponentComplex_le C)) (by
        intro s hs
        obtain ⟨t, ht, htc, hst⟩ := hpure s hs.1
        exact ⟨t, K.edgeComponentComplex_coface C hs ht hst, htc, hst⟩)
      (K.edgeComponentComplex_isPathConnected C).isConnected (by
        intro v hv
        rw [← SimplicialComplex.faceLink_singleton_eq_link,
          K.edgeComponentComplex_vertex_link C hv, SimplicialComplex.faceLink_singleton_eq_link]
        exact hlinks v (K.edgeComponentComplex_le C hv)) (by
        intro s hs hsc
        rw [K.edgeComponentComplex_cofaces C hs 3]
        exact hcofaces s hs.1 hsc)
  choose r hr hboundary hsphere using hex
  refine ⟨r, fun C => ⟨hr C, ?_, hsphere C⟩⟩
  rintro ⟨s, hs, hsc, hc⟩
  apply hboundary C
  refine ⟨s, hs, hsc, ?_⟩
  rwa [K.edgeComponentComplex_cofaces C hs 3]

end Geometry.SimplicialComplex
