import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Contacts.WholeCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.ExceptionSchedule



set_option autoImplicit false
open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier} {R Fmark : Set M}

namespace MarkedSurfacePositionData

def repairPairs (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark) : Set (V × V) :=
  {z | z ∈ D.relation.space ∧ D.projected z.1 ∈ D.exceptionalValues}

theorem repairPairs_finite (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark) :
    D.repairPairs.Finite := by
  apply D.exceptional_pairs_finite.subset
  intro z hz
  have h := D.relation_space.subset hz.1
  refine ⟨D.source_space.symm.subset h.1, D.source_space.symm.subset h.2.1, ?_, hz.2⟩
  simpa only [projected, endpoint, ← D.final_state, Function.comp_apply] using h.2.2.1

theorem repairPairs_subset_relation (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark) :
    D.repairPairs ⊆ D.relation.space := fun _ hz => hz.1

theorem mem_repairPairs_iff
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    {x y : V} (hx : x ∈ D.K.space) (hy : y ∈ D.K.space) (hne : x ≠ y)
    (hxy : D.projected x = D.projected y) :
    (x, y) ∈ D.repairPairs ↔ D.projected x ∈ D.exceptionalValues := by
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  apply D.relation_space.symm.subset
  refine ⟨D.source_space.subset hx, D.source_space.subset hy, ?_, hne⟩
  simpa only [projected, endpoint, ← D.final_state, Function.comp_apply] using hxy

end MarkedSurfacePositionData
end Geometry.OriginalPLTower
