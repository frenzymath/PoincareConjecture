import PoincareConjecture.Definitions.M72FiniteReconstruction
import Mathlib.Data.Finite.Sigma











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v w

namespace PoincareConjecture

namespace SmoothDisjointUnionData






def reindex {n n' : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}}
    (D : SmoothDisjointUnionData pieces C) (e : Fin n' ≃ Fin n) :
    SmoothDisjointUnionData (fun j : Fin n' => pieces (e j)) C where
  region := fun j => D.region (e j)
  region_open := fun j => D.region_open (e j)
  region_closed := fun j => D.region_closed (e j)
  identify := fun j => D.identify (e j)
  pairwise_disjoint := by
    intro i j hij
    exact D.pairwise_disjoint (e i) (e j) (fun h => hij (e.injective h))
  cover := by
    apply Set.Subset.antisymm
    · intro x _
      exact Set.mem_univ x
    · intro x _
      have hx : x ∈ ⋃ i, D.region i := by
        rw [D.cover]
        exact Set.mem_univ x
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨e.symm i, by simpa using hi⟩



def reindexOfEq {n n' : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {pieces' : Fin n' → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}}
    (D : SmoothDisjointUnionData pieces C) (e : Fin n' ≃ Fin n)
    (he : ∀ j, pieces' j = pieces (e j)) :
    SmoothDisjointUnionData pieces' C := by
  have h : pieces' = fun j => pieces (e j) := funext he
  rw [h]
  exact D.reindex e

end SmoothDisjointUnionData

namespace SmoothFiniteConnectedSumAssembly



def reindex {n n' : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces C) (e : Fin n' ≃ Fin n) :
    SmoothFiniteConnectedSumAssembly (fun j : Fin n' => pieces (e j)) C where
  initial := S.initial
  disjoint_union := S.disjoint_union.reindex e
  operations := S.operations



def reindexOfEq {n n' : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {pieces' : Fin n' → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces C) (e : Fin n' ≃ Fin n)
    (he : ∀ j, pieces' j = pieces (e j)) :
    SmoothFiniteConnectedSumAssembly pieces' C where
  initial := S.initial
  disjoint_union := S.disjoint_union.reindexOfEq e he
  operations := S.operations

end SmoothFiniteConnectedSumAssembly



structure M72IndexedAssembly {ι : Type v}
    (pieces : ι → GeneralizedSliceCarrier.{u}) (C : GeneralizedSliceCarrier.{u}) where
  count : ℕ
  index : Fin count ≃ ι
  assembly : SmoothFiniteConnectedSumAssembly (fun j => pieces (index j)) C

namespace M72IndexedAssembly



def ofAssembly {n : ℕ} {pieces : Fin n → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}}
    (S : SmoothFiniteConnectedSumAssembly pieces C) : M72IndexedAssembly pieces C where
  count := n
  index := Equiv.refl (Fin n)
  assembly := S



def reindex {ι : Type v} {κ : Type w}
    {pieces : ι → GeneralizedSliceCarrier.{u}}
    {pieces' : κ → GeneralizedSliceCarrier.{u}}
    {C : GeneralizedSliceCarrier.{u}}
    (S : M72IndexedAssembly pieces C) (e : ι ≃ κ)
    (he : ∀ i, pieces' (e i) = pieces i) : M72IndexedAssembly pieces' C where
  count := S.count
  index := S.index.trans e
  assembly := S.assembly.reindexOfEq (Equiv.refl (Fin S.count)) (fun j => he (S.index j))



noncomputable def transportTarget {ι : Type v}
    {pieces : ι → GeneralizedSliceCarrier.{u}}
    {A B : GeneralizedSliceCarrier.{u}}
    (S : M72IndexedAssembly pieces A)
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞) :
    M72IndexedAssembly pieces B where
  count := S.count
  index := S.index
  assembly := S.assembly.transportTarget d

end M72IndexedAssembly







instance m72EventIndexFintype {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I) :
    Fintype (M72EventIndex I L) := inferInstance



noncomputable instance m72NonSurvivorIndexFintype {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I)
    (e : M72EventIndex I L) :
    Fintype (M72NonSurvivorIndex I L e) := by
  unfold M72NonSurvivorIndex
  exact Fintype.ofFinite _



noncomputable instance m72SummandIndexFintype {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I) :
    Fintype (M72SummandIndex I L) := by
  unfold M72SummandIndex
  exact inferInstance



noncomputable def m72SummandEnumeration
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I) :
    Fin (Fintype.card (M72SummandIndex I L)) ≃ M72SummandIndex I L :=
  (Fintype.equivFin (M72SummandIndex I L)).symm

end PoincareConjecture
