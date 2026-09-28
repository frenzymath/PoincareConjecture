import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexExtension

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {K L : SimplicialComplex ℝ E}
  [Fintype K.faces] [Fintype L.faces] {T : BoundaryTriangleFibers K L}

local notation "I" => Icc (0 : ℝ) 1

structure BoundaryVertexFamily (P : BoundaryEdgeFamily T) where
  chart : ∀ p : L.vertices,
    ((L.barycentricDualBlock {(p : E)}).space ×ˢ I : Set (E × ℝ)) ≃ₜ
      (K.barycentricDualBlock {(p : E)}).space
  piecewiseAffine : ∀ p, (chart p).IsFinitePL
  central : ∀ (p : L.vertices) (x : E) (hx : x ∈ (L.barycentricDualBlock {(p : E)}).space),
    (chart p ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x
  boundary : ∀ (p : L.vertices)
    (x : ((L.barycentricDualBlock {(p : E)}).space ×ˢ I : Set (E × ℝ))),
    (chart p x : E) ∈ L.space ↔ (x : E × ℝ).2 = 0
  keep_edge : ∀ (p : L.vertices) (s : Finset E), s ∈ L.faces → s.card = 2 →
    ∀ hps : (p : E) ∈ s,
    ∀ (x : E × ℝ) (hx : x ∈ (L.barycentricDualBlock s).space ×ˢ I),
      (chart p ⟨x, ⟨space_subset_of_le (L.barycentricDualBlock_antitone
        (Finset.singleton_subset_iff.mpr hps)) hx.1, hx.2⟩⟩ : E) = P.map s x

theorem BoundaryEdgeFamily.exists_vertex_family [FiniteDimensional ℝ E]
    (P : BoundaryEdgeFamily T) (hLK : L ≤ K)
    (hLcard : ∀ u ∈ L.faces, u.card ≤ 3)
    (hfull : ∀ u ∈ K.faces, (∀ p ∈ u, p ∈ L.vertices) → u ∈ L.faces)
    (hB : ∀ p : L.vertices, Nonempty (BoundaryVertexHalfBall K L p)) :
    Nonempty (BoundaryVertexFamily P) := by
  classical
  have hex (p : L.vertices) := P.exists_vertex_extension hLK hLcard hfull
    p.property (Classical.choice (hB p))
  choose H hH hcentral hboundary hkeep using hex
  exact ⟨⟨H, hH, hcentral, hboundary, hkeep⟩⟩

end Geometry.SimplicialComplex
