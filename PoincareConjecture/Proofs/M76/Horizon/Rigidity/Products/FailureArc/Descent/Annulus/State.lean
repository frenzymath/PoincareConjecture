import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.PlanarReparametrization
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.EssentialAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.SourceGeometry



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76

local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

noncomputable def planarAnnulusRim {X : Type*} [TopologicalSpace X]
    (f : C(Ann, X)) (b : Bool) : C(Circle, X) :=
  f.comp ⟨Dehn.annulusRimPoint b, Dehn.continuous_annulusRimPoint b⟩

end PoincareConjecture.M76

namespace Geometry.OriginalPLTower

open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}

structure MarkedEssentialPlanarAnnulus (t : Stage e S f r C)
    (R : Set M) (F : Bool → Set M) where
  map : P2 → t.Carrier
  original : C(Ann, R)
  original_eq : ∀ x : Ann, (original x : M) = t.projection (map x)
  piecewiseAffine : PolyhedralPLInCharts t.charts map Ann
  embedding : IsEmbedding (fun x : Ann => map x)
  proper : ∀ x : Ann, map x ∈ frontier (t.projection ⁻¹' R) ↔
    depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1
  mark : ∀ b z, t.projection (map (annulusRimPoint b z)) ∈ F b
  essential : ∀ b, ¬ (planarAnnulusRim original b).Nullhomotopic

theorem MarkedEssentialPlanarAnnulus.region
    {t : Stage e S f r C} {R : Set M} {F : Bool → Set M}
    (A : MarkedEssentialPlanarAnnulus t R F) :
    MapsTo A.map Ann (t.projection ⁻¹' R) := by
  intro x hx
  change t.projection (A.map x) ∈ R
  rw [← A.original_eq ⟨x, hx⟩]
  exact (A.original ⟨x, hx⟩).property

end Geometry.OriginalPLTower
