import PoincareConjecture.Statements.M63CurveEstimates

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

noncomputable def M62FlowConclusion.toM63AmbientGeometry (E : M62FlowConclusion F) :
    M63AmbientGeometry F where
  K0 := E.K0
  K1 := E.K1
  K2 := E.K2
  nonnegative := E.nonnegative
  bounds := E.bounds
  product := fun circumference h => (Classical.choice (E.circle_products circumference h)).product
  product_identities := fun circumference h =>
    (Classical.choice (E.circle_products circumference h)).product_identities
  product_bounds := fun circumference h =>
    (Classical.choice (E.circle_products circumference h)).bounds

theorem m63AmbientGeometry_nonempty [T2Space M] [SecondCountableTopology M]
    (hM62 : M62CurveEvolutionTheory.{u}) (hcompact : IsCompact (Set.univ : Set M)) :
    Nonempty (M63AmbientGeometry F) := by
  obtain ⟨E⟩ := hM62 n M a b F hcompact
  exact ⟨E.toM63AmbientGeometry⟩

end PoincareConjecture
