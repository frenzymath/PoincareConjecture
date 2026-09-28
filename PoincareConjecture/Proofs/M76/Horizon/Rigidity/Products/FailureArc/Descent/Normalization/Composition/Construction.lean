import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.BoundaryRepair
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.Schedule

set_option autoImplicit false
open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => PLAnnularStrip.squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => PLAnnularStrip.depth 8 z = -1 ∨
  PLAnnularStrip.depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ P2} {j : P2 → t.Carrier} {R Fmark : Set M}

theorem MarkedSurfacePositionData.nonempty_finite_marked_annulus_repairs
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    (hAnn : D.K.space = Ann) (hRim : A₀.space = Rim)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark)) :
    Nonempty (FiniteMarkedSurfaceRepairs D) := by
  have hboundary : A₀.space = frontier K₀.space := by
    rw [← D.source_space, hAnn, hRim]
    ext x
    exact (PoincareConjecture.M76.Dehn.Annuli.mem_frontier_planar_annulus_iff x).symm
  apply D.assemble_finite_marked_repairs
  intro a b hab hpair W hWopen haW hW
  by_cases ha : D.projected a ∈ frontier (s.projection ⁻¹' R)
  · have haRim : (a : P2) ∈ A₀.space := (D.projected_proper a a.property).mp ha
    exact D.nonempty_marked_annulus_boundary_exception_repair hAnn hRim he hF hopen
      a b hab haRim hpair hWopen haW hW
  · have haint : D.projected a ∈ interior (s.projection ⁻¹' R) := by
      by_contra hn
      exact ha ⟨subset_closure (D.projected_region a.property), hn⟩
    exact D.nonempty_marked_interior_exception_repair hboundary hF a b hab hpair haint
      hWopen haW hW

end Geometry.OriginalPLTower
