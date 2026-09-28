import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.State

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem MarkedEssentialPlanarAnnulus.exists_original_embedded_annulus
    {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
    {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C R : Set M}
    {F : Bool → Set M} {s : Stage e S f r C}
    (A : MarkedEssentialPlanarAnnulus s R F) (hs : IsOpenEmbedding s.projection) :
    ∃ j : P2 → M, PolyhedralPLInCharts e j Ann ∧
      IsEmbedding (fun x : Ann => j x) ∧ MapsTo j Ann R ∧
      (∀ x : Ann, j x = (A.original x : M)) ∧
      (∀ x : Ann, j x ∈ frontier R ↔ depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1) ∧
      (∀ b z, j (annulusRimPoint b z) ∈ F b) ∧
      ∀ b, ¬ (planarAnnulusRim A.original b).Nullhomotopic := by
  refine ⟨s.projection ∘ A.map, ?_, hs.isEmbedding.comp A.embedding,
    A.region, fun x => (A.original_eq x).symm, ?_, A.mark, A.essential⟩
  · exact A.piecewiseAffine.project s.chartIndex s.projection.continuous s.chart_source
      (fun k x _ => congrFun (s.chart_forward k) x)
  · intro x
    have hh := A.proper x
    rwa [s.frontier_region] at hh

end Geometry.OriginalPLTower
