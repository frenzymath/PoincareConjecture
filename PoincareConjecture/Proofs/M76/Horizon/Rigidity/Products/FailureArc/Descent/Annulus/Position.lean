import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.State
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.PlanarPosition

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}

theorem MarkedEssentialPlanarAnnulus.rim_mark
    {t : Stage e S f r C} {R : Set M} {F : Bool → Set M}
    (A : MarkedEssentialPlanarAnnulus t R F)
    (x : Ann) (hx : depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1) :
    t.projection (A.map x) ∈ F false ∪ F true := by
  rcases hx with hx | hx
  · have hm : x ∈ range (annulusRimPoint false) := by
      rw [range_annulusRimPoint]
      exact hx
    obtain ⟨z, rfl⟩ := hm
    exact Or.inl (A.mark false z)
  · have hm : x ∈ range (annulusRimPoint true) := by
      rw [range_annulusRimPoint]
      exact hx
    obtain ⟨z, rfl⟩ := hm
    exact Or.inr (A.mark true z)

theorem MarkedEssentialPlanarAnnulus.exists_position_data
    {s t : Stage e S f r C} (step : Step s t)
    {R : Set M} {F : Bool → Set M}
    (A : MarkedEssentialPlanarAnnulus t R F)
    (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b)) :
    ∃ K B : SimplicialComplex ℝ P2,
      K.space = Ann ∧ B.space = {x | depth 8 x = -1 ∨ depth 8 x = 1} ∧
      Nonempty (MarkedSurfacePositionData step K B A.map R (F false ∪ F true)) := by
  exact step.exists_planar_annulus_position_data he
    (union_subset (hF false) (hF true)) ((hopen false).union (hopen true))
    A.piecewiseAffine A.embedding A.region A.proper A.rim_mark

end Geometry.OriginalPLTower
