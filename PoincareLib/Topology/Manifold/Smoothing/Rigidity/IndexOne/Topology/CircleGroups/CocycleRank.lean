import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Topology.CircleGroups.CharacterKernel
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A cyclic fundamental group bounds the original cocycle rank

Evaluate the constructed cover character at a cyclic generator. The
kernel consists of actual vertex coboundaries by the vertex-path
construction. Rank-nullity then bounds the excess of the original
closed edge cochains over the vertex coboundaries by one.
See Hatcher, Algebraic Topology, pp. 68--70 and 196--197.
-/

set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)

/-- Cyclicity of the actual fundamental group bounds the first mod-two
incidence rank, with every original edge and vertex retained. -/
theorem finrank_closed_le_finrank_coboundaries_add_one_of_isCyclic
    [PathConnectedSpace A.barycentricSpace] (hvertex : ∀ i : ι, {i} ∈ A.faces)
    (x : A.barycentricSpace) [IsCyclic (FundamentalGroup A.barycentricSpace x)] :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary A)) + 1 := by
  classical
  obtain ⟨g, hg⟩ := exists_zpow_surjective (FundamentalGroup A.barycentricSpace x)
  let E := closedCochainEvaluation A g
  have hker (z : LinearMap.ker (edgeCoboundary A)) (hz : E z = 0) :
      (z : Edge A → ZMod 2) ∈ LinearMap.range (vertexCoboundary A) := by
    apply mem_range_vertexCoboundary_of_coboundary A z z.property
    let c := cocycleOfClosed A z z.property
    apply c.isCoboundary_of_loopCharacter_eq_one hvertex x
    intro q
    obtain ⟨n, rfl⟩ := hg q
    have hcg : c.loopCharacter x g = 1 :=
      congrArg Multiplicative.ofAdd hz
    rw [map_zpow, hcg, one_zpow]
  let T : LinearMap.ker E →ₗ[ZMod 2] LinearMap.range (vertexCoboundary A) :=
    { toFun := fun z => ⟨z.val.val, hker z.val z.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : Function.Injective T := by
    intro z w h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : LinearMap.range (vertexCoboundary A) => t.val) h
  have hk := LinearMap.finrank_le_finrank_of_injective hT
  have hr : Module.finrank (ZMod 2) (LinearMap.range E) ≤ 1 := by
    simpa using (LinearMap.range E).finrank_le
  have heq := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) E
  omega

end PreAbstractSimplicialComplex.ModTwoCochains
