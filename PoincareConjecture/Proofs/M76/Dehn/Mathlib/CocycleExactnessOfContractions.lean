import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CoverSections
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SimplicialCocycleConnected
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ModTwoCocycleOfClosed
import PoincareConjecture.Proofs.M76.Mathlib.FiniteBarycentricCoordinates

set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {ι : Type*} [Fintype ι] {A : PreAbstractSimplicialComplex ι}

private theorem not_injective_projection [Nonempty A.barycentricSpace]
    (c : A.ModTwoEdgeCocycle) : ¬Function.Injective c.bundle.proj := by
  classical
  intro hinj
  let q : A.barycentricSpace := Classical.arbitrary _
  have heq : (⟨q, (0 : ZMod 2)⟩ : c.bundle.TotalSpace) = ⟨q, (1 : ZMod 2)⟩ := hinj rfl
  have hzero : (0 : ZMod 2) = 1 :=
    congrArg (fun z : c.bundle.TotalSpace => (z.2 : ZMod 2)) heq
  exact zero_ne_one hzero

theorem isCoboundary_of_contractible [ContractibleSpace A.barycentricSpace]
    (c : A.ModTwoEdgeCocycle) (hvertex : ∀ i : ι, {i} ∈ A.faces) :
    c.IsCoboundary := by
  classical
  by_contra hc
  let : ConnectedSpace c.bundle.TotalSpace := c.connectedSpace_of_not_isCoboundary hvertex hc
  obtain ⟨s, hs⟩ := c.isCoveringMap.exists_continuous_section_of_contractible
    (fun q => ⟨⟨q, (0 : ZMod 2)⟩, rfl⟩)
  exact c.not_injective_projection
    (c.isCoveringMap.injective_of_continuous_section s hs (Classical.arbitrary _))

theorem isCoboundary_of_simplyConnected
    [SimplyConnectedSpace A.barycentricSpace] [LocallyPathConnectedSpace A.barycentricSpace]
    (c : A.ModTwoEdgeCocycle) (hvertex : ∀ i : ι, {i} ∈ A.faces) :
    c.IsCoboundary := by
  classical
  by_contra hc
  let : ConnectedSpace c.bundle.TotalSpace := c.connectedSpace_of_not_isCoboundary hvertex hc
  obtain ⟨s, hs⟩ := c.isCoveringMap.exists_continuous_section_of_simplyConnected
    (fun q => ⟨⟨q, (0 : ZMod 2)⟩, rfl⟩)
  exact c.not_injective_projection
    (c.isCoveringMap.injective_of_continuous_section s hs (Classical.arbitrary _))

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)

theorem ker_edgeCoboundary_eq_range_of_contractible
    [ContractibleSpace A.barycentricSpace] (hvertex : ∀ i : ι, {i} ∈ A.faces) :
    LinearMap.ker (edgeCoboundary A) = LinearMap.range (vertexCoboundary A) := by
  apply le_antisymm
  · intro z hz
    exact mem_range_vertexCoboundary_of_coboundary A z hz
      ((cocycleOfClosed A z hz).isCoboundary_of_contractible hvertex)
  · rintro _ ⟨a, rfl⟩
    exact edgeCoboundary_vertexCoboundary A a

theorem ker_edgeCoboundary_eq_range_of_simplyConnected
    [SimplyConnectedSpace A.barycentricSpace] [LocallyPathConnectedSpace A.barycentricSpace]
    (hvertex : ∀ i : ι, {i} ∈ A.faces) :
    LinearMap.ker (edgeCoboundary A) = LinearMap.range (vertexCoboundary A) := by
  apply le_antisymm
  · intro z hz
    exact mem_range_vertexCoboundary_of_coboundary A z hz
      ((cocycleOfClosed A z hz).isCoboundary_of_simplyConnected hvertex)
  · rintro _ ⟨a, rfl⟩
    exact edgeCoboundary_vertexCoboundary A a

end PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

open PreAbstractSimplicialComplex.ModTwoCochains

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.vertices]

theorem edge_exact_of_contractible [ContractibleSpace K.space] :
    LinearMap.ker (edgeCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex) =
      LinearMap.range
        (vertexCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex) := by
  let : ContractibleSpace K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace :=
    K.finiteBarycentricHomeomorph.contractibleSpace
  exact ker_edgeCoboundary_eq_range_of_contractible _ K.vertexAbstractComplex.singleton_mem

theorem edge_exact_of_simplyConnected
    [SimplyConnectedSpace K.space] [LocallyPathConnectedSpace K.space] :
    LinearMap.ker (edgeCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex) =
      LinearMap.range
        (vertexCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex) := by
  let : SimplyConnectedSpace
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace :=
    K.finiteBarycentricHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace :=
    K.finiteBarycentricHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ker_edgeCoboundary_eq_range_of_simplyConnected _ K.vertexAbstractComplex.singleton_mem

end Geometry.SimplicialComplex
