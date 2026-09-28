import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BarycentricOpenStars
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Instances.ZMod
import Mathlib.Data.Set.Card










set_option autoImplicit false

open Set Topology

namespace FiberBundleCore





theorem t2SpaceTotal {ι B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
    [T2Space B] [T2Space F] (Z : FiberBundleCore ι B F) : T2Space Z.TotalSpace := by
  constructor
  intro x y hxy
  by_cases hbase : Z.proj x = Z.proj y
  · let T := Z.localTriv (Z.indexAt (Z.proj x))
    have hx : x ∈ T.source := Z.mem_baseSet_at (Z.proj x)
    have hy : y ∈ T.source := by
      change Z.proj y ∈ Z.baseSet (Z.indexAt (Z.proj x))
      rw [← hbase]
      exact Z.mem_baseSet_at (Z.proj x)
    have hne : T x ≠ T y := fun h => hxy (T.toOpenPartialHomeomorph.injOn hx hy h)
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hne
    refine ⟨T.source ∩ T ⁻¹' U, T.source ∩ T ⁻¹' V,
      T.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage T.open_source hU,
      T.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage T.open_source hV,
      ⟨hx, hxU⟩, ⟨hy, hyV⟩, ?_⟩
    exact disjoint_left.mpr fun _ hzU hzV => disjoint_left.mp hUV hzU.2 hzV.2
  · obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hbase
    exact ⟨Z.proj ⁻¹' U, Z.proj ⁻¹' V,
      hU.preimage Z.continuous_proj, hV.preimage Z.continuous_proj,
      hxU, hyV, hUV.preimage Z.proj⟩

end FiberBundleCore

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [Fintype ι]




structure ModTwoEdgeCocycle (A : PreAbstractSimplicialComplex ι) where
  value : ι → ι → ZMod 2
  diagonal : ∀ i, value i i = 0
  compose : ∀ s ∈ A.faces, ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s,
    value i j + value j k = value i k

namespace ModTwoEdgeCocycle

variable {A : PreAbstractSimplicialComplex ι}



def IsCoboundary (c : A.ModTwoEdgeCocycle) : Prop :=
  ∃ a : ι → ZMod 2, ∀ s ∈ A.faces, ∀ i ∈ s, ∀ j ∈ s,
    c.value i j = a i + a j





noncomputable def bundle (c : A.ModTwoEdgeCocycle) :
    FiberBundleCore ι A.barycentricSpace (ZMod 2) where
  baseSet := A.openVertexStar
  isOpen_baseSet := A.isOpen_openVertexStar
  indexAt q := Classical.choose (A.exists_mem_openVertexStar q)
  mem_baseSet_at q := Classical.choose_spec (A.exists_mem_openVertexStar q)
  coordChange i j _ b := b + c.value i j
  coordChange_self i _ _ b := by rw [c.diagonal i, add_zero]
  continuousOn_coordChange i j :=
    ((continuous_of_discreteTopology : Continuous (fun b : ZMod 2 => b + c.value i j)).comp
      continuous_snd).continuousOn
  coordChange_comp i j k q hq b := by
    obtain ⟨s, hs, hvertices⟩ := A.exists_face_containing_openStars q
    have hc := c.compose s hs i (hvertices i hq.1.1) j (hvertices j hq.1.2)
      k (hvertices k hq.2)
    exact (add_assoc b (c.value i j) (c.value j k)).trans (congrArg (b + ·) hc)



theorem isCoveringMap (c : A.ModTwoEdgeCocycle) : IsCoveringMap c.bundle.proj :=
  FiberBundle.isCoveringMap (F := ZMod 2) (E := c.bundle.Fiber)



instance totalSpaceT2 (c : A.ModTwoEdgeCocycle) : T2Space c.bundle.TotalSpace :=
  c.bundle.t2SpaceTotal



theorem fiber_ncard (c : A.ModTwoEdgeCocycle) (q : A.barycentricSpace) :
    (c.bundle.proj ⁻¹' {q}).ncard = 2 := by
  let H := (c.bundle.localTrivAt q).preimageSingletonHomeomorph
    (c.bundle.mem_baseSet_at q)
  change Nat.card (c.bundle.proj ⁻¹' {q}) = 2
  rw [Nat.card_congr H.toEquiv, Nat.card_eq_fintype_card, ZMod.card]



theorem trivialization_change (c : A.ModTwoEdgeCocycle) {i j : ι}
    {q : A.barycentricSpace} (hi : q ∈ A.openVertexStar i)
    (hj : q ∈ A.openVertexStar j) (b : ZMod 2) :
    c.bundle.localTriv j ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (q, b)) =
      (q, b + c.value i j) := by
  obtain ⟨s, hs, hvertices⟩ := A.exists_face_containing_openStars q
  have hc := c.compose s hs i (hvertices i hi)
    (c.bundle.indexAt q) (hvertices _ (c.bundle.mem_baseSet_at q)) j (hvertices j hj)
  change (q, (b + c.value i (c.bundle.indexAt q)) + c.value (c.bundle.indexAt q) j) =
    (q, b + c.value i j)
  rw [add_assoc, hc]

end ModTwoEdgeCocycle

end PreAbstractSimplicialComplex
