import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.GroupRank.Arithmetic
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.GroupRank.Characters
import PoincareConjecture.Proofs.M76.Mathlib.FiniteBarycentricCoordinates
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteCarrierLocalPathConnected
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters









set_option autoImplicit false

open Set Geometry AbstractSimplicialComplex
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

open Classical in
theorem exists_surface_three_coordinate_evaluation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) [Fintype K.vertices]
    (hK : K.faces.Finite) (hconn : IsConnected K.space) (q : K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace)
    (f : FundamentalGroup K.space (K.finiteBarycentricHomeomorph q) →* Multiplicative (Fin 3 → ℤ))
    (hf : Function.Injective f) :
    ∃ (eval : LinearMap.ker (edgeCoboundary
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex) →ₗ[ZMod 2]
          (Fin 3 → ZMod 2))
      (T : LinearMap.ker eval →ₗ[ZMod 2] LinearMap.range (vertexCoboundary
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex)), Function.Injective T := by
  let : ConnectedSpace K.space := isConnected_iff_connectedSpace.mp hconn
  let : LocallyPathConnectedSpace K.space := K.locallyPathConnectedSpace_of_finite hK
  let : PathConnectedSpace K.space := .of_locallyPathConnectedSpace
  let H := K.finiteBarycentricHomeomorph
  let : PathConnectedSpace K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace :=
    H.symm.surjective.pathConnectedSpace H.symm.continuous
  let e := H.fundamentalGroupMulEquiv q
  exact exists_three_coordinate_evaluation_of_injective _ K.vertexAbstractComplex.singleton_mem q
    (f.comp e.toMonoidHom) (hf.comp e.injective)

open Classical in


theorem surfaceEulerCount_eq_zero_of_injective_integer_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) [Fintype K.vertices] (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 →
      t ≠ u → ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (q : K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace)
    [Nontrivial (FundamentalGroup K.space (K.finiteBarycentricHomeomorph q))]
    (f : FundamentalGroup K.space (K.finiteBarycentricHomeomorph q) →* Multiplicative (Fin 3 → ℤ))
    (hf : Function.Injective f) : K.surfaceEulerCount = 0 := by
  obtain ⟨eval, T, hT⟩ := exists_surface_three_coordinate_evaluation K hK hconn q f hf
  exact surfaceEulerCount_eq_zero_of_character_rank K hK hpure hconn hlinks hcofaces
    number hnumber sign hcancel (K.finiteBarycentricHomeomorph q) eval T hT

open Classical in


theorem surfaceEulerCount_eq_zero_of_injective_integer_three_and_signs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 3)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.faceLink {v}).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (number : K.vertices ↪ ℕ)
    (sign : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2)
    (hcancel : ∀ t u : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
      t ≠ u → ∀ s : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
      s.val ⊆ t.val → s.val ⊆ u.val →
        (sign t + boundaryFaceParity number t.val s.val) +
          (sign u + boundaryFaceParity number u.val s.val) = 1)
    (x : K.space) [Nontrivial (FundamentalGroup K.space x)]
    (f : FundamentalGroup K.space x →* Multiplicative (Fin 3 → ℤ))
    (hf : Function.Injective f) : K.surfaceEulerCount = 0 := by
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  have hlinks' : ∀ v ∈ K.vertices, IsConnected (K.link v).space := by
    simpa only [K.faceLink_singleton_eq_link] using hlinks
  have hpure' : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, hc⟩ := hpure s hs
    exact ⟨t, ht, hc, hst⟩
  have hrank : Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary A)) + 3 := by
    obtain ⟨q, rfl⟩ := K.finiteBarycentricHomeomorph.surjective x
    obtain ⟨eval, T, hT⟩ := exists_surface_three_coordinate_evaluation K hK hconn q f hf
    exact finrank_closed_le_finrank_coboundaries_add_three eval T hT
  have hidentity := K.closed_surface_incidence_rank_identity hK hpure' hconn hlinks'
    hcofaces
  have htwo (s : Edge A) : (triangleCofaces A s).card = 2 := by
    rw [K.triangleCofaces_card_eq_original]
    exact hcofaces _ s.property.1 (by simpa using s.property.2)
  have hlinkgraph (v : K.vertices) :
      (K.faceLink {v.val}).vertexAbstractComplex.edgeGraph.Preconnected :=
    ((K.faceLink {v.val}).connected_edgeGraph_of_isConnected
      (K.finite_faceLink_faces hK _) (hlinks v v.property)).preconnected
  have heven : Even K.surfaceEulerCount := by
    obtain ⟨k, hk⟩ := K.even_euler_count_of_all_edge_signs hpure
      (by intro v; convert! hlinkgraph v)
      number sign (by intro t u htu s hst hsu; convert! hcancel t u htu s hst hsu) htwo
    rw [K.surfaceEulerCount_eq_vertex_counts]
    refine ⟨(k : ℤ) - Nat.card (Edge A), ?_⟩
    simp only [Nat.card_eq_fintype_card, A] at hk ⊢
    omega
  have hne : K.surfaceEulerCount ≠ 2 := by
    intro h
    let : SimplyConnectedSpace K.space :=
      K.simplyConnectedSpace_of_surfaceEulerCount_eq_two hK hpure' hconn hlinks' hcofaces h
    exact not_nontrivial (FundamentalGroup K.space x) inferInstance
  have hle := K.surfaceEulerCount_le_two_sub_boundary_circle_count hK hpure' hconn
    hlinks' (fun i : Empty ↦ i.elim) (fun i ↦ i.elim) (fun i ↦ i.elim)
    (fun i ↦ i.elim) (fun i ↦ i.elim)
    (by intro s hs hc; simpa using hcofaces s hs hc)
  norm_num at hle
  dsimp only at hidentity
  obtain ⟨k, hk⟩ := heven
  dsimp [A] at hrank
  omega

end PoincareConjecture.M76
