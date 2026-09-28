import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.GroupRank.OriginalResidual

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

theorem PLDomain.exists_original_torus_candidate_on_frontier
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    {R S : Set X0} (he : PLDomain e R) (hR : IsCompact R)
    (hS : S ⊆ frontier R) (x : S)
    (hcomponent : connectedComponentIn (frontier R) x = S)
    (hnt : Nontrivial (FundamentalGroup S x))
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X0)) x)) :
    ∃ C : OriginalTorusEulerCandidate e R (frontier R), C.surface = S := by
  classical
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  have hxF : (x : X0) ∈ frontier R := hS x.property
  obtain ⟨M⟩ := he.nonempty_frontier_residual_model hR
    ⟨x, he.closed.frontier_subset hxF⟩ isClosed_empty isClosed_frontier
    (by simp) (empty_union _).symm ⟨x, hxF⟩
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (M.cover.symm ▸ hxF)
  have hiS : M.components i = S :=
    ((M.component i).2.2.2 x hxi).symm.trans hcomponent
  let y : M.components i := ⟨x, hxi⟩
  have hnt' : Nontrivial (FundamentalGroup (M.components i) y) := by
    subst S
    exact hnt
  have hinj' : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(M.components i, X0)) y) := by
    subst S
    exact hinj
  have hres := M.residual_eq_two_of_ambient_injective e he.cover he.compatible
    he hR isClosed_empty isClosed_frontier (by simp)
    (empty_union _).symm i y hnt' hinj'
  exact ⟨⟨M, i, hres⟩, hiS⟩

end PoincareConjecture.M76
