import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Data
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Reduction.SourceGeometry



set_option autoImplicit false
open Set Geometry Topology

namespace Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t} {j : P2 → t.Carrier}
  {R Fmark : Set M} {a b : PLAnnularStrip.squareAnnulus 8 1}
  {W : Set s.Carrier} {ε : ℝ}
  (N : PlanarAnnulusBoundaryMotion step j R Fmark a b W ε)

theorem positive_parameter_interior {v : V3} (hv : v ∈ N.branchComplex.space)
    (hvJ : v ∈ interior N.support.space) (hvpos : 0 < (N.coordinates v).1.1) :
    N.parameter v ∈ interior (N.parameter '' N.branchComplex.space) := by
  have hvS := N.branch_space.subset hv
  have hnot : N.parameter v ∉ _root_.frontier (PLAnnularStrip.squareAnnulus 8 1) := by
    intro h
    have hB := (N.parameter_rim v hvS).mpr
      ((PoincareConjecture.M76.Dehn.Annuli.mem_frontier_planar_annulus_iff _).mp h)
    exact hvpos.ne' (N.boundary_level.subset hB).2
  have hint : N.parameter v ∈ interior (PLAnnularStrip.squareAnnulus 8 1) := by
    by_contra h
    exact hnot ⟨subset_closure (N.parameter_range hvS), h⟩
  rw [N.branch_space]
  exact N.parameter_interior v hvS hvJ hint

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
