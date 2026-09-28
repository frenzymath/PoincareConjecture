import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.OriginalTorusLeafRimIntervals

set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.PeriodicSquare

open Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

def ownerIntervalStatement
    (J : SimplicialComplex ℝ E) [Fintype J.faces] (S : Set J.vertices)
    (a b : J.vertices) : Prop :=
  ∃ t ∈ J.faces, ∃ u ∈ J.faces,
    t.card = 3 ∧ u.card = 3 ∧
    ({a.val, b.val} : Finset E) ⊆ t ∧ ({a.val, b.val} : Finset E) ⊆ u ∧
    t.centroid ℝ id ≠ u.centroid ℝ id ∧
    IsFinitePLBallPair ℝ (J.barycentricDualBlock {a.val, b.val}).space
      {t.centroid ℝ id, u.centroid ℝ id} ∧
    ({a.val, b.val} : Finset E).centroid ℝ id ∈
      (J.barycentricDualBlock {a.val, b.val}).space \
        {t.centroid ℝ id, u.centroid ℝ id} ∧
    (J.barycentricDualBlock {a.val, b.val}).space ∩
      (⋃ z ∈ J.vertices \ {a.val, b.val},
        (J.barycentricDualBlock {z}).space) =
      {t.centroid ℝ id, u.centroid ℝ id} ∧
    (J.barycentricDualBlock {a.val, b.val}).space ⊆ J.vertexDualRim S

theorem exists_two_residual_owner_intervals
    {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
    [Fintype K.barycentricSubdivision.faces]
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (P : SimpleGraph K.vertices)
    (D : SimpleGraph (Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
    (r : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).incidenceSubdivision ↪g
      K.barycentricSubdivision.vertexAbstractComplex.edgeGraph)
    {S : Set K.barycentricSubdivision.vertices}
    (hS : S = Set.range ((dualIncidenceRestriction K.vertexAbstractComplex P D hD).trans r))
    (s₀ s₁ : (complementaryTriangleGraph
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex P).edgeSet)
    (hs₀ : s₀.val ∉ D.edgeSet) (hs₁ : s₁.val ∉ D.edgeSet) (hne : s₀ ≠ s₁) :
    s₀ ≠ s₁ ∧
    ∃ q₀ q₁ : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
      q₀ ∈ s₀.val ∧ q₁ ∈ s₁.val ∧
      (∀ _ : Bool, ownerIntervalStatement K.barycentricSubdivision S
        (r (Sum.inl q₀)) (r (Sum.inr s₀))) ∧
      (∀ _ : Bool, ownerIntervalStatement K.barycentricSubdivision S
        (r (Sum.inl q₁)) (r (Sum.inr s₁))) := by
  obtain ⟨q₀, hq₀, _⟩ := OriginalTriangleCopies.complementary_edge_owner_selected_unselected
    hcofaces P D hD r hS s₀ hs₀
  obtain ⟨q₁, hq₁, _⟩ := OriginalTriangleCopies.complementary_edge_owner_selected_unselected
    hcofaces P D hD r hS s₁ hs₁
  have h₀ := residual_owner_interval_on_leaf_rim hpure hcofaces P D hD r hS s₀ hs₀ q₀ hq₀
  have h₁ := residual_owner_interval_on_leaf_rim hpure hcofaces P D hD r hS s₁ hs₁ q₁ hq₁
  exact ⟨hne, q₀, q₁, hq₀, hq₁, fun _ => by simpa [ownerIntervalStatement] using h₀,
    fun _ => by simpa [ownerIntervalStatement] using h₁⟩

end PoincareConjecture.M76.PeriodicSquare
