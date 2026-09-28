import PoincareConjecture.Statements.M39ComparisonMap
import PoincareConjecture.Proofs.M39.Prop15_12_Assembly
import PoincareConjecture.Proofs.M39.Prop15_12_BranchAssembly
import PoincareConjecture.Proofs.M39.Prop15_12_Gluing

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem repairedComparisonMap : RepairedComparisonMapTheory.{u} := by
  refine ⟨⟨1, zero_lt_one, ?_⟩⟩
  intro g₀ D _hε
  refine ⟨{ comparison := ?_ }⟩
  intro T hT hNonempty I _hdelta _hheight
  obtain ⟨B⟩ := M39.comparisonBranches_nonempty I
  obtain ⟨G⟩ := M39.comparisonExtension_of_branches I B
  exact ⟨M39.comparisonConclusionOfExtension I G⟩

end PoincareConjecture
