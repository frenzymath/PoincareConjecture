import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Loops.OriginalFrontierEssentialRim
import PoincareConjecture.Proofs.M76.Wall.OriginalComponentSphere











set_option autoImplicit false

open Set Metric Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1

theorem original_frontier_component_sphere_or_essential_rim
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    (C : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space)
    {S F : Set X} (hSF : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S)
    (HC : (A.edgeComponentComplex C).space ≃ₜ S) (g : E → X)
    (hHC : ∀ z, (HC z : X) = g z)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space) :
    Nonempty (ChartwisePLSphere e S) ∨
    ∃ (n : ℕ) (P : Polygon E (n + 3)) (a : Q ≃ₜ P.boundary ℝ)
      (d : V2 → E) (gamma : C(Q, F)),
      P.HasSimplicialEdges ∧ Function.Injective P ∧
      (∀ i, P.edgeVertices i ∈ (A.edgeComponentComplex C).faces) ∧
      P.boundary ℝ ⊆ (A.edgeComponentComplex C).space ∧
      a.IsFinitePL ∧ FinitePiecewiseAffineOn d Q ∧
      (∀ x : Q, d x = (a x : E)) ∧ d '' Q = P.boundary ℝ ∧
      (∀ x : Q, (gamma x : X) = g (d x)) ∧
      (∀ x : Q, (gamma x : X) ∈ S) ∧
      Topology.IsEmbedding gamma ∧ PolyhedralPLInCharts e (g ∘ d) Q ∧
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Dehn.squareRimLoop.map gamma.continuous)) ≠ 1 := by
  classical
  let J := A.edgeComponentComplex C
  have hA : A.faces.Finite := hK.subset hAK
  have hJK : J ≤ K := (A.edgeComponentComplex_le C).trans hAK
  have hJ : J.faces.Finite := hK.subset hJK
  have hgJ : PolyhedralPLInCharts e g J.space :=
    hg.comp_finitePiecewiseAffineOn J hJ
      ((J.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)).finitePiecewiseAffineOn hJ)
      (SimplicialComplex.space_subset_of_le hJK)
  by_cases hpositive : Nat.card J.vertices +
      Nat.card (Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex) <
      Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2
  · exact Or.inr (exists_original_frontier_essential_rim e A hA C hpure hcofaces
      hlinks hSF hcomponent HC g hHC hgJ hpositive)
  · obtain ⟨P, _, _, D, _, _, residual, _, _, hcount⟩ :=
      A.exists_edgeComponent_trees_with_residual_edges hA C hpure hcofaces hlinks
    have hzero : Nat.card J.vertices +
        Nat.card (Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex) =
        Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 := by
      have hcount' : Nat.card J.vertices +
          Nat.card (Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex) +
          residual.card =
          Nat.card (Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2 := by
        convert! hcount
      omega
    have himage : g '' J.space = S := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [← hHC ⟨z, hz⟩]
        exact (HC ⟨z, hz⟩).property
      · intro hx
        obtain ⟨z, hz⟩ := HC.surjective ⟨x, hx⟩
        exact ⟨z, z.property, (hHC z).symm.trans (congrArg Subtype.val hz)⟩
    rw [← himage]
    exact Or.inl (exists_original_component_sphere_of_count K A hK hAK hg hgi
      hpure hcofaces hlinks C hzero)

end PoincareConjecture.M76
