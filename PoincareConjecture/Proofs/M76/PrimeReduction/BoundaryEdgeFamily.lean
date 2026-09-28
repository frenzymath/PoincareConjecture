import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryEdgeProducts









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype L.faces]

local notation "I" => Icc (0 : ℝ) 1



structure BoundaryEdgeFamily (T : BoundaryTriangleFibers K L) where
  map : Finset E → E × ℝ → E
  piecewiseAffine : ∀ s ∈ L.faces, s.card = 2 →
    FinitePiecewiseAffineOn (map s) ((L.barycentricDualBlock s).space ×ˢ I)
  injective : ∀ s ∈ L.faces, s.card = 2 →
    InjOn (map s) ((L.barycentricDualBlock s).space ×ˢ I)
  image_eq : ∀ s ∈ L.faces, s.card = 2 →
    map s '' ((L.barycentricDualBlock s).space ×ˢ I) = (K.barycentricDualBlock s).space
  central : ∀ s ∈ L.faces, s.card = 2 →
    ∀ x ∈ (L.barycentricDualBlock s).space, map s (x, 0) = x
  keep_triangle : ∀ s ∈ L.faces, s.card = 2 → ∀ t ∈ L.faces,
    s ⊆ t → t.card = 3 → ∀ r ∈ I, map s (t.centroid ℝ id, r) = T.map t r
  boundary : ∀ s ∈ L.faces, s.card = 2 →
    ∀ x ∈ (L.barycentricDualBlock s).space ×ˢ I, map s x ∈ L.space ↔ x.2 = 0




theorem BoundaryTriangleFibers.exists_edge_family [FiniteDimensional ℝ E] [DecidableEq E]
    (T : BoundaryTriangleFibers K L) (hLK : L ≤ K)
    (hLcard : ∀ t ∈ L.faces, t.card ≤ 3)
    (hfull : ∀ t ∈ K.faces, (∀ p ∈ t, p ∈ L.vertices) → t ∈ L.faces)
    (hends : ∀ s ∈ L.faces, s.card = 2 → (L.faceLink s).vertices.ncard = 2)
    (hlinks : ∀ s ∈ L.faces, s.card = 2 →
      IsFinitePLBallPair ℝ (K.faceLink s).space (L.faceLink s).space) :
    Nonempty (BoundaryEdgeFamily T) := by
  classical
  let J := {s : Finset E // s ∈ L.faces ∧ s.card = 2}
  have hex (s : J) := T.exists_edge_product hLK hLcard hfull
    s.property.1 s.property.2 (hends s s.property.1 s.property.2)
    (hlinks s s.property.1 s.property.2)
  choose f hf hi him hc hkeep hb hrim using hex
  let g : Finset E → E × ℝ → E := fun s =>
    if h : s ∈ L.faces ∧ s.card = 2 then f ⟨s, h⟩ else fun _ => 0
  have hval (s : J) : g s = f s := by
    simp only [g, dif_pos s.property]
    rfl
  refine ⟨⟨g, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs hsc
    rw [hval ⟨s, hs, hsc⟩]
    exact hf ⟨s, hs, hsc⟩
  · intro s hs hsc
    rw [hval ⟨s, hs, hsc⟩]
    exact hi ⟨s, hs, hsc⟩
  · intro s hs hsc
    rw [hval ⟨s, hs, hsc⟩]
    exact him ⟨s, hs, hsc⟩
  · intro s hs hsc
    rw [hval ⟨s, hs, hsc⟩]
    exact hc ⟨s, hs, hsc⟩
  · intro s hs hsc
    rw [hval ⟨s, hs, hsc⟩]
    exact hkeep ⟨s, hs, hsc⟩
  · intro s hs hsc
    rw [hval ⟨s, hs, hsc⟩]
    exact hb ⟨s, hs, hsc⟩

end Geometry.SimplicialComplex
