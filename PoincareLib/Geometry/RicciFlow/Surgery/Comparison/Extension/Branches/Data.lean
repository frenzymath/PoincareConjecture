import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Extension.Branches.Collars
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Map
/-!
# The branch decomposition used to assemble Proposition 15.12

The topology of Remark 15.13, Morgan--Tian p. 365, supplies a connected
retained root and disjoint outward open regions at its boundary spheres.
This internal record contains only the resulting sets and collar sides;
the comparison map is subsequently constructed by open-cover gluing.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.SurgeryComparison

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  (I : RepairedComparisonMapInput D T hT)

local notation "E" => D.flow.event T hT

/-- The actual closed root and its uniquely assigned outward regions.
Every field follows from the separating-sphere argument in Remark 15.13,
p. 365. This record has no comparison map or metric-bound field and is
constructed internally from the unchanged public input. -/
structure ComparisonBranches where
  caps : Set (Fin (E).cap_count)
  root : Set I.parent.carrier.carrier
  root_closed : IsClosed root
  retained_eq : I.retained = interior root
  outward : caps → Set I.parent.carrier.carrier
  outward_open : ∀ i, IsOpen (outward i)
  outward_disjoint_root : ∀ i, Disjoint (outward i) root
  outward_disjoint : Pairwise (fun i j => Disjoint (outward i) (outward j))
  cover : root ∪ ⋃ i, outward i = Set.univ
  frontier_root : frontier root = ⋃ i : caps, parentNeckSphere E i.1 I.parent
  negative_root : ∀ i : caps,
    parentNeckRegion E i.1 I.parent (-((E).necks i.1).neck.epsilon⁻¹) 0 ⊆ root
  positive_outward : ∀ i : caps,
    parentNeckRegion E i.1 I.parent 0 ((E).necks i.1).neck.epsilon⁻¹ ⊆ outward i
  local_output_in_child : ∀ i : caps,
    Set.range ((E).local_embed i.1) ⊆ Set.range I.child.inclusion

end PoincareMT.SurgeryComparison
