import PoincareLib.Topology.Manifold.Smoothing.Dehn.Coverings.Mathlib.CoverSections
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.SimplicialCocycleConnected
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Topology.Mathlib.ModTwoCocycleOfClosed
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.FiniteBarycentricCoordinates

/-!
# Literal edge exactness from the actual local link spaces

The constructed nontrivial cocycle cover would be connected. An actual
section from a contraction or sphere lifting makes its projection
injective, contradicting the two literal points in each fiber.
The original incidence maps are unchanged. See Hatcher pp. 60, 68--70,
105 and Dehn derivation 015.
-/

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

/-- A contraction of the actual barycentric carrier rules out the
constructed connected cocycle cover. No local-connectivity premise
is needed. See Hatcher Proposition 1.30 and Dehn derivation 015. -/
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

/-- The actual simply connected, locally path connected carrier
similarly rules out a nontrivial cocycle by its constructed cover.
See Hatcher pp. 68--70 and Dehn derivation 015. -/
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

/-- A contraction gives exactness of the same original edge incidence
map by the literal cocycle of each closed cochain. See derivation 015. -/
theorem ker_edgeCoboundary_eq_range_of_contractible
    [ContractibleSpace A.barycentricSpace] (hvertex : ∀ i : ι, {i} ∈ A.faces) :
    LinearMap.ker (edgeCoboundary A) = LinearMap.range (vertexCoboundary A) := by
  apply le_antisymm
  · intro z hz
    exact mem_range_vertexCoboundary_of_coboundary A z hz
      ((cocycleOfClosed A z hz).isCoboundary_of_contractible hvertex)
  · rintro _ ⟨a, rfl⟩
    exact edgeCoboundary_vertexCoboundary A a

/-- Simply connected and locally path connected actual carriers give
the identical finite incidence exactness. See Dehn derivation 015. -/
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

/-- Transport the actual geometric contraction through the original
barycentric homeomorphism, retaining every original vertex label.
See Dehn derivation 015. -/
theorem edge_exact_of_contractible [ContractibleSpace K.space] :
    LinearMap.ker (edgeCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex) =
      LinearMap.range
        (vertexCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex) := by
  let : ContractibleSpace K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace :=
    K.finiteBarycentricHomeomorph.contractibleSpace
  exact ker_edgeCoboundary_eq_range_of_contractible _ K.vertexAbstractComplex.singleton_mem

/-- The same exact original vertex labels are retained when the
geometric carrier has the actual sphere lifting properties.
See Dehn derivation 015. -/
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
