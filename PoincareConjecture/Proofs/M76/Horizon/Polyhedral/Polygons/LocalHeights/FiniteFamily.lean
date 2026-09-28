import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.Polygons

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_finite_boundary_family {κ : Type*} [Finite κ]
    (n : κ → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    {Z : Set E} (hcover : Z = ⋃ i, (P i).boundary ℝ)
    (hdisjoint : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))) :
    ∃ S : Set (Set E), S.Finite ∧
      (∀ s ∈ S, ∃ n : ℕ, ∃ p : Polygon E (n + 3),
        Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = s) ∧
      S.PairwiseDisjoint id ∧ Z = ⋃ s ∈ S, s ∧ ∀ s ∈ S, s ⊆ Z := by
  let S : Set (Set E) := range (fun i => (P i).boundary ℝ)
  refine ⟨S, finite_range _, ?_, ?_, ?_, ?_⟩
  · rintro s ⟨i, rfl⟩
    exact ⟨n i, P i, (hP i).1, (hP i).2, rfl⟩
  · rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩ hne
    exact hdisjoint (fun h => hne (congrArg (fun i => (P i).boundary ℝ) h))
  · rw [hcover]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨(P i).boundary ℝ, ⟨i, rfl⟩, hi⟩
    · intro hx
      obtain ⟨s, ⟨i, rfl⟩, hxs⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨i, hxs⟩
  · rintro s ⟨i, rfl⟩ x hx
    exact hcover.symm.subset (mem_iUnion.mpr ⟨i, hx⟩)

end Polygon

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem exists_finite_triangleSlice_polygon_family (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (hK : K.faces.Finite)
    (hnozero : ∀ e ∈ K.faces, e.card = 2 → ∃ q ∈ e, q ∉ K.triangleZeroVertices A)
    (hcofaces : ∀ e : K.triangleCrossingEdges A,
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t}.ncard = 2)
    (hfans : ∀ q : K.triangleZeroVertices A, ∃ a b u v : E,
      ({q.val, a, u} : Finset E) ∈ K.faces ∧ ({q.val, a, u} : Finset E).card = 3 ∧
      ({q.val, a, v} : Finset E) ∈ K.faces ∧ ({q.val, a, v} : Finset E).card = 3 ∧
      ({q.val, b, u} : Finset E) ∈ K.faces ∧ ({q.val, b, u} : Finset E).card = 3 ∧
      ({q.val, b, v} : Finset E) ∈ K.faces ∧ ({q.val, b, v} : Finset E).card = 3 ∧
      (∀ t ∈ K.faces, t.card = 3 → q.val ∈ t →
        t = {q.val, a, u} ∨ t = {q.val, a, v} ∨ t = {q.val, b, u} ∨ t = {q.val, b, v}) ∧
      a ≠ b ∧
      A {q.val, a, u} a ≠ 0 ∧ A {q.val, a, u} a = A {q.val, a, v} a ∧
      A {q.val, b, u} b ≠ 0 ∧ A {q.val, b, u} b = A {q.val, b, v} b ∧
      A {q.val, a, u} u < 0 ∧ 0 < A {q.val, a, v} v ∧
      A {q.val, b, u} u < 0 ∧ 0 < A {q.val, b, v} v) :
    ∃ S : Set (Set E), S.Finite ∧
      (∀ s ∈ S, ∃ n : ℕ, ∃ p : Polygon E (n + 3),
        Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = s) ∧
      S.PairwiseDisjoint id ∧ K.triangleZeroSet A = ⋃ s ∈ S, s ∧
      (∀ s ∈ S, s ⊆ K.triangleZeroSet A) ∧
      (K.triangleZeroSet A ⊆ interior K.space → ∀ s ∈ S, s ⊆ interior K.space) := by
  have hvertices : K.vertices.Finite := hK.preimage Finset.singleton_injective.injOn
  have hzeros : (K.triangleZeroVertices A).Finite := hvertices.subset (fun _ hq => hq.1)
  let : Finite (K.triangleZeroVertices A) := hzeros.to_subtype
  let : Finite (K.triangleCrossingEdges A) := (K.finite_triangleCrossingEdges A hK).to_subtype
  obtain ⟨n, P, hP, hcover, hdisjoint⟩ :=
    K.exists_triangleSlice_polygons_of_marked_fans hA hK hnozero hcofaces hfans
  obtain ⟨S, hS, hpolygons, hpairwise, hcoverS, hsub⟩ :=
    Polygon.exists_finite_boundary_family n P hP hcover hdisjoint
  exact ⟨S, hS, hpolygons, hpairwise, hcoverS, hsub,
    fun h s hs => (hsub s hs).trans h⟩

end Geometry.SimplicialComplex
