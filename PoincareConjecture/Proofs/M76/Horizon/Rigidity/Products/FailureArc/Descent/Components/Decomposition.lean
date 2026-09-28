import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Components.PairedComponents

set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace PoincareConjecture.M76.Dehn.Annuli

open Classical in

structure SourceDoubleComponents
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (f : E → X) (S Q : Set E) (R : Set X) where
  source : SimplicialComplex ℝ E
  source_finite : source.faces.Finite
  source_space : source.space = S
  graph : SimplicialComplex ℝ E
  partner : graph.space ≃ₜ graph.space
  finite : graph.faces.Finite
  space : graph.space = doubleLocusOn f S
  partnerPL : partner.IsFinitePL
  partnerInvPL : partner.symm.IsFinitePL
  involutive : Function.Involutive partner
  free : ∀ x : graph.space, (partner x : E) ≠ x
  value : ∀ x : graph.space, f (partner x) = f x
  unique : ∀ (x : graph.space) (y : E), y ∈ S → (x : E) ≠ y →
    f x = f y → y = (partner x : E)
  partner_rim : ∀ x : graph.space, (partner x : E) ∈ Q ↔ (x : E) ∈ Q
  face_card : ∀ a ∈ graph.faces, a.card ≤ 2
  degree : ∀ v : graph.vertices, (graph.vertexAbstractComplex.edgeGraph.neighborSet v).ncard =
    if (v : E) ∈ Q then 1 else 2
  rim : graph.space ∩ Q = Subtype.val '' {v : graph.vertices |
    (graph.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1}
  pieces : graph.vertexAbstractComplex.edgeGraph.ConnectedComponent → Set E
  mate : Equiv.Perm graph.vertexAbstractComplex.edgeGraph.ConnectedComponent
  finite_components : Finite graph.vertexAbstractComplex.edgeGraph.ConnectedComponent
  geometric : ∀ A, pieces A = A.toSimpleGraph.segmentCarrier (fun v => (v.val : E))
  cover : graph.space = ⋃ A, pieces A
  disjoint : Pairwise (fun A B => Disjoint (pieces A) (pieces B))
  topology : ∀ A, IsCompact (pieces A) ∧ IsConnected (pieces A) ∧
    IsClopen ((Subtype.val : graph.space → E) ⁻¹' pieces A)
  models : ∀ A, IsFinitePLBallPair ℝ (pieces A) (pieces A ∩ Q) ∨
    ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = pieces A ∧ Disjoint (pieces A) Q
  mate_involutive : Function.Involutive mate
  partner_component : ∀ A (x : graph.space), (x : E) ∈ pieces A ↔
    (partner x : E) ∈ pieces (mate A)
  image_mate : ∀ A, f '' pieces (mate A) = f '' pieces A
  image_disjoint : ∀ A B, A ≠ B → mate A ≠ B →
    Disjoint (f '' pieces A) (f '' pieces B)
  interval : ∀ A, IsFinitePLBallPair ℝ (pieces A) (pieces A ∩ Q) →
    mate A ≠ A ∧
    ∃ (alpha : I ≃ₜ pieces A) (beta : I ≃ₜ pieces (mate A)) (arc : ℝ → X),
      alpha.IsFinitePL ∧ beta.IsFinitePL ∧
      (∀ u : I, ∃ hx : (alpha u : E) ∈ graph.space,
        (beta u : E) = (partner ⟨alpha u, hx⟩ : E)) ∧
      pieces A ∩ Q = {(alpha 0 : E), (alpha 1 : E)} ∧
      pieces (mate A) ∩ Q = {(beta 0 : E), (beta 1 : E)} ∧
      IsEmbedding (fun u : I => arc u) ∧
      PolyhedralPLInCharts e arc (Icc (0 : ℝ) 1) ∧
      (∀ u : I, arc u = f (alpha u) ∧ arc u = f (beta u)) ∧
      (∀ x ∈ S, f x ∈ range (fun u : I => arc u) ↔
        x ∈ pieces A ∪ pieces (mate A)) ∧
      (∀ u : I, arc u ∈ frontier R ↔ u = 0 ∨ u = 1) ∧
      ∀ u : I, u ≠ 0 → u ≠ 1 → arc u ∈ interior R
  crossings : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
    Nonempty (RawSourceCrossing e f S R x y)

theorem nonempty_sourceDoubleComponents
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {f : E → X} {R : Set X}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (Q : Set E)
    (hf : PolyhedralPLInCharts e f K.space) (hR : MapsTo f K.space R)
    (hclosed : IsClosed (doubleLocusOn f K.space))
    (hproper : ∀ x ∈ K.space, f x ∈ frontier R ↔ x ∈ Q)
    (hcross : ∀ x ∈ K.space, ∀ y ∈ K.space, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f K.space R x y))
    (hunique : ∀ x ∈ K.space, ∀ y ∈ K.space, ∀ z ∈ K.space,
      x ≠ y → x ≠ z → f x = f y → f x = f z → y = z) :
    Nonempty (SourceDoubleComponents e f K.space Q R) := by
  obtain ⟨G, partner, hG, hGs, hp, hpinv, hp2, hfree, hvalue, hmate, hprim,
    hcard, hdegree, hrim⟩ :=
    exists_finite_proper_double_graph he K hK Q hf hR hclosed hproper hcross hunique
  obtain ⟨pieces, mate, hfin, hgeo, hcover, hdis, htop, hmodels, hm2,
    hmem, himage, himagedis, harc⟩ :=
    exists_paired_proper_source_components hf hR hproper G partner hG hGs hp hp2
      (fun x h => hfree x (congrArg Subtype.val h)) (fun x => (hvalue x).symm)
      hmate hprim hcard hdegree hrim
  exact ⟨⟨K, hK, rfl, G, partner, hG, hGs, hp, hpinv, hp2, hfree, hvalue, hmate, hprim,
    hcard, hdegree, hrim, pieces, mate, hfin, hgeo, hcover, hdis, htop, hmodels,
    hm2, hmem, himage, himagedis, harc, hcross⟩⟩

end PoincareConjecture.M76.Dehn.Annuli
