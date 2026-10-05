import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates

/-!
# Ambient geometry retained from M62

The corrected ambient constants of Morgan--Tian's 2015 correction, pp. 6-8,
and the circle products of MT2007, pp. 446-449, are already outputs of M62.
This conversion retains those exact constants and product geometry for M63.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}

/-- Retain M62's actual bounds and circle products, chosen in the order required
by corrected Corollary 19.10 and the ramp construction, MT2007 pp. 446-449. -/
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

/-- M62 supplies the primitive geometry of M63 for any admissible compact flow;
the local-flow and ramp arguments remain separate M63 obligations.
Sources: MT2007 pp. 446-449 and MT2015Correction pp. 6-8. -/
theorem m63AmbientGeometry_nonempty [T2Space M] [SecondCountableTopology M]
    (hM62 : M62CurveEvolutionTheory.{u}) (hcompact : IsCompact (Set.univ : Set M)) :
    Nonempty (M63AmbientGeometry F) := by
  obtain ⟨E⟩ := hM62 n M a b F hcompact
  exact ⟨E.toM63AmbientGeometry⟩

end PoincareMT
