import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem isCompact_coordinate_image_Icc (N : EpsilonNeck g) (a b : ℝ)
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) :
    IsCompact (N.coordinate_map '' (univ ×ˢ Icc a b)) := by
  apply ((isCompact_univ : IsCompact (univ : Set UnitTwoSphere)).prod
    isCompact_Icc).image_of_continuousOn
  apply N.coordinate_map_smooth.continuousOn.mono
  rintro ⟨q, s⟩ ⟨hq, hs⟩
  exact ⟨hq, ha.trans_le hs.1, hs.2.trans_lt hb⟩

variable {ι : Type v} (N : ι → EpsilonNeck g) (a b : ι → ℝ)

theorem iUnion_carrier_eq_iUnion_closedSlab
    (ha : ∀ i, -(N i).epsilon⁻¹ < a i)
    (hb : ∀ i, b i < (N i).epsilon⁻¹)
    (hcover : ∀ i x, x ∈ (N i).carrier →
      ∃ j, x ∈ (N j).carrier ∧ ((N j).coordinate_inverse x).2 ∈ Icc (a j) (b j)) :
    (⋃ i, (N i).carrier) =
      ⋃ i, (N i).coordinate_map '' (univ ×ˢ Icc (a i) (b i)) := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj, ht⟩ := hcover i x hi
    exact mem_iUnion.mpr ⟨j, (N j).coordinate_inverse x,
      ⟨mem_univ _, ht⟩, (N j).coordinate_map_inverse hj⟩
  · intro x hx
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, (N i).coordinate_map_mem
      ⟨hz.1, (ha i).trans_le hz.2.1, hz.2.2.trans_lt (hb i)⟩⟩

variable [Finite ι]

theorem isCompact_iUnion_carrier_of_retained_cover
    (ha : ∀ i, -(N i).epsilon⁻¹ < a i)
    (hb : ∀ i, b i < (N i).epsilon⁻¹)
    (hcover : ∀ i x, x ∈ (N i).carrier →
      ∃ j, x ∈ (N j).carrier ∧ ((N j).coordinate_inverse x).2 ∈ Icc (a j) (b j)) :
    IsCompact (⋃ i, (N i).carrier) := by
  rw [iUnion_carrier_eq_iUnion_closedSlab N a b ha hb hcover]
  exact isCompact_iUnion fun i =>
    (N i).isCompact_coordinate_image_Icc (a i) (b i) (ha i) (hb i)

theorem isClopen_iUnion_carrier_of_retained_cover [T2Space M]
    (ha : ∀ i, -(N i).epsilon⁻¹ < a i)
    (hb : ∀ i, b i < (N i).epsilon⁻¹)
    (hcover : ∀ i x, x ∈ (N i).carrier →
      ∃ j, x ∈ (N j).carrier ∧ ((N j).coordinate_inverse x).2 ∈ Icc (a j) (b j)) :
    IsClopen (⋃ i, (N i).carrier) :=
  ⟨(isCompact_iUnion_carrier_of_retained_cover N a b ha hb hcover).isClosed,
    isOpen_iUnion fun i => (N i).carrier_open⟩

theorem iUnion_carrier_eq_univ_of_retained_cover [T2Space M]
    [PreconnectedSpace M] [Nonempty ι]
    (ha : ∀ i, -(N i).epsilon⁻¹ < a i)
    (hb : ∀ i, b i < (N i).epsilon⁻¹)
    (hcover : ∀ i x, x ∈ (N i).carrier →
      ∃ j, x ∈ (N j).carrier ∧ ((N j).coordinate_inverse x).2 ∈ Icc (a j) (b j)) :
    (⋃ i, (N i).carrier) = univ := by
  apply (isClopen_iUnion_carrier_of_retained_cover N a b ha hb hcover).eq_univ
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨(N i).center, mem_iUnion.mpr
    ⟨i, (N i).central_sphere_subset (N i).center_on_central_sphere⟩⟩

theorem subset_iUnion_carrier_of_retained_cover [T2Space M]
    (ha : ∀ i, -(N i).epsilon⁻¹ < a i)
    (hb : ∀ i, b i < (N i).epsilon⁻¹)
    (hcover : ∀ i x, x ∈ (N i).carrier →
      ∃ j, x ∈ (N j).carrier ∧ ((N j).coordinate_inverse x).2 ∈ Icc (a j) (b j))
    {X : Set M} (hX : IsPreconnected X)
    (hmeet : (X ∩ ⋃ i, (N i).carrier).Nonempty) :
    X ⊆ ⋃ i, (N i).carrier :=
  hX.subset_isClopen
    (isClopen_iUnion_carrier_of_retained_cover N a b ha hb hcover) hmeet

theorem iUnion_carrier_eq_connectedComponent_of_retained_cover
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [Nonempty ι]
    (ha : ∀ i, -(N i).epsilon⁻¹ < a i)
    (hb : ∀ i, b i < (N i).epsilon⁻¹)
    (hcover : ∀ i x, x ∈ (N i).carrier →
      ∃ j, x ∈ (N j).carrier ∧ ((N j).coordinate_inverse x).2 ∈ Icc (a j) (b j))
    (hoverlap : ∀ i j, Relation.ReflTransGen
      (fun k l => ((N k).carrier ∩ (N l).carrier).Nonempty) i j)
    {x : M} (hx : x ∈ ⋃ i, (N i).carrier) :
    (⋃ i, (N i).carrier) = connectedComponent x := by
  have hconn := IsConnected.iUnion_of_reflTransGen
    (fun i => (N i).isConnected_carrier) hoverlap
  exact Subset.antisymm (hconn.subset_connectedComponent hx)
    ((isClopen_iUnion_carrier_of_retained_cover N a b ha hb hcover).connectedComponent_subset hx)

end PoincareConjecture.EpsilonNeck
