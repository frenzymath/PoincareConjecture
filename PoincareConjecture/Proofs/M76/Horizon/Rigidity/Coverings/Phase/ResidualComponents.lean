import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.SourcePhaseResidualModels
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.FrontierResidualModel

variable {X Y ι : Type*} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {N F : Set X}

def componentInclusion (M : FrontierResidualModel e N F) (i : Fin M.count) :
    C(M.components i, F) := ContinuousMap.inclusion (M.component i).2.2.1

theorem isOpenEmbedding_componentInclusion
    (M : FrontierResidualModel e N F) (i : Fin M.count) :
    IsOpenEmbedding (M.componentInclusion i) := by
  classical
  let inc := M.componentInclusion i
  have hi : Function.Injective inc := by
    intro x y h
    apply Subtype.ext
    simpa [inc, componentInclusion, ContinuousMap.inclusion] using
      congrArg (fun z : F => (z : X)) h
  let B : Set X := ⋃ j : Fin M.count, if j = i then ∅ else M.components j
  have hB : IsClosed B := isClosed_iUnion_of_finite fun j => by
    split_ifs
    · exact isClosed_empty
    · exact (M.component j).1.isClosed
  have hrange : range inc = (Subtype.val ⁻¹' B : Set F)ᶜ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩ hy
      obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      by_cases hji : j = i
      · simp [hji] at hj
      · have hj' : (y : X) ∈ M.components j := by
          simpa [hji, inc, componentInclusion, ContinuousMap.inclusion] using hj
        exact disjoint_left.mp (M.disjoint hji) hj' y.property
    · intro hx
      have hxF : (x : X) ∈ ⋃ j, M.components j := M.cover.symm ▸ x.property
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxF
      have hji : j = i := by
        by_contra hji
        exact hx (mem_iUnion.mpr ⟨j, by simpa [hji] using hj⟩)
      exact ⟨⟨x, hji ▸ hj⟩, Subtype.ext rfl⟩
  let : CompactSpace (M.components i) := isCompact_iff_compactSpace.mp (M.component i).1
  exact ⟨(inc.continuous.isClosedEmbedding hi).isEmbedding,
    hrange ▸ (hB.preimage continuous_subtype_val).isOpen_compl⟩

theorem isCoveringMap_component
    (M : FrontierResidualModel e N F) (g : C(F, Y)) (hg : IsCoveringMap g)
    (i : Fin M.count) : IsCoveringMap (g.comp (M.componentInclusion i)) := by
  let : CompactSpace (M.components i) := isCompact_iff_compactSpace.mp (M.component i).1
  exact isLocalHomeomorph_iff_isCoveringMap.mp
    (hg.isLocalHomeomorph.comp (M.isOpenEmbedding_componentInclusion i).isLocalHomeomorph)

end PoincareConjecture.M76.FrontierResidualModel
