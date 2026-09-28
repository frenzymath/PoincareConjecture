import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.OriginalComponentSigns
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.Darts.EulerParity
import PoincareConjecture.Proofs.M76.Wall.OriginalComponentResidualEdges

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains AbstractSimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_frontier_component_genus_count
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K A : SimplicialComplex ℝ E) (hAK : A ≤ K) (hA : A.faces.Finite)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space)
    (g : E → X) (N : Set X)
    (hgi : InjOn g K.space) (hfront : MapsTo g A.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ D : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans D ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space D.source ∧
      (K.closedStar p).AffineOnFaces (D ∘ g) ∧
      (D.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ D.source, y ∈ N ↔ 0 ≤ ell (D y)))
    (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {R C F T : Set X} (HC : (A.edgeComponentComplex c).space ≃ₜ T)
    (hHC : ∀ z, (HC z : X) = g z)
    (hTF : T ⊆ F) (hFU : F ⊆ R \ C)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) :
    let J := A.edgeComponentComplex c
    let L := J.vertexAbstractComplex.toPreAbstractSimplicialComplex
    ∃ (genus : ℕ) (number : J.vertices ↪ ℕ) (sigma : Triangle L → ZMod 2),
      Nat.card J.vertices + Nat.card (Triangle L) + 2 * genus = Nat.card (Edge L) + 2 ∧
      ∀ t u : Triangle L, t ≠ u → ∀ s : Edge L,
        s.val ⊆ t.val → s.val ⊆ u.val →
        (sigma t + boundaryFaceParity number t.val s.val) +
          (sigma u + boundaryFaceParity number u.val s.val) = 1 := by
  classical
  let J := A.edgeComponentComplex c
  let : Fintype J.vertices :=
    (J.finite_vertices_of_finite_faces (hA.subset (A.edgeComponentComplex_le c))).fintype
  obtain ⟨number, sigma, hcancel⟩ := exists_original_frontier_component_all_edge_signs
    e hcover hcompat K A hAK hA g N hgi hfront hstars c HC hHC hTF hFU hloops
  have hlinkgraphs : ∀ v : J.vertices,
      (J.faceLink {v.val}).vertexAbstractComplex.edgeGraph.Preconnected := by
    intro v
    rw [A.edgeComponentComplex_vertex_link c v.property]
    exact ((A.faceLink {v.val}).connected_edgeGraph_of_isConnected
      (SimplicialComplex.finite_faceLink_faces hA _)
      (hlinks v.val (A.edgeComponentComplex_le c v.property))).preconnected
  have heven := J.even_euler_count_of_all_edge_signs
    (A.edgeComponentComplex_pure c hpure) (by intro v; convert! hlinkgraphs v)
    number sigma (by intro t u htu s hst hsu; convert! hcancel t u htu s hst hsu)
    (A.edgeComponentComplex_triangle_cofaces c hcofaces)
  obtain ⟨P, _, _, D, _, _, residual, _, _, hcount⟩ :=
    A.exists_edgeComponent_trees_with_residual_edges hA c hpure hcofaces hlinks
  have heven' : Even (Nat.card J.vertices +
      Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      Nat.card (Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex)) := by
    simpa only [Nat.card_eq_fintype_card] using heven
  have hcount' : Nat.card J.vertices +
      Nat.card (Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + residual.card =
      Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 := by
    convert! hcount
  obtain ⟨k, hk⟩ := heven'
  have hresidual : Even residual.card := by
    apply Nat.even_iff.mpr
    omega
  obtain ⟨genus, hgenus⟩ := hresidual
  refine ⟨genus, number, sigma, ?_, hcancel⟩
  omega

end PoincareConjecture.M76
