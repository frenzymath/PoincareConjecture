import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.BoundaryReduction.Construction



set_option autoImplicit false
open Set Geometry Topology
open PoincareConjecture.M76

namespace Geometry.OriginalPLTower

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M (Fin 3 → ℝ)}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C R : Set M}
  {F : Bool → Set M}

theorem MarkedEssentialPlanarAnnulus.nonempty_predecessor
    {s t : Stage e S f r C} (A : MarkedEssentialPlanarAnnulus t R F)
    (step : Step s t) (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true)) :
    Nonempty (MarkedEssentialPlanarAnnulus s R F) := by
  obtain ⟨B⟩ := A.nonempty_ordinary_projection step he hF hopen hdis
  exact B.nonempty_embedded he hF hopen hdis

theorem MarkedEssentialPlanarAnnulus.nonempty_of_reaches
    {s t : Stage e S f r C} (A : MarkedEssentialPlanarAnnulus t R F)
    (hreach : Reaches s t) (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true)) :
    Nonempty (MarkedEssentialPlanarAnnulus s R F) := by
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨A⟩
  | head hstep _ ih =>
    obtain ⟨step⟩ := hstep
    obtain ⟨B⟩ := ih
    exact B.nonempty_predecessor step he hF hopen hdis

end Geometry.OriginalPLTower
