import PoincareConjecture.Definitions.Ch15.SurgeryTopology

set_option autoImplicit false

universe u v

namespace PoincareConjecture

variable {n : Nat} {pieces : Fin n -> GeneralizedSliceCarrier.{u}}
  {A C : GeneralizedSliceCarrier.{u}}

def SmoothDisjointUnionData.toAssembly (U : SmoothDisjointUnionData pieces C) :
    SmoothFiniteConnectedSumAssembly pieces C where
  initial := C
  disjoint_union := U
  operations := Relation.ReflTransGen.refl

def SmoothFiniteConnectedSumAssembly.tail (S : SmoothFiniteConnectedSumAssembly pieces A)
    (h : SmoothConnectedSumStep A C) : SmoothFiniteConnectedSumAssembly pieces C where
  initial := S.initial
  disjoint_union := S.disjoint_union
  operations := Relation.ReflTransGen.tail S.operations h

def SmoothFiniteConnectedSumAssembly.trans (S : SmoothFiniteConnectedSumAssembly pieces A)
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) :
    SmoothFiniteConnectedSumAssembly pieces C where
  initial := S.initial
  disjoint_union := S.disjoint_union
  operations := Relation.ReflTransGen.trans S.operations h

def SmoothDisjointUnionData.reindexM38 {m : Nat}
    (U : SmoothDisjointUnionData pieces C) (e : Equiv (Fin m) (Fin n)) :
    SmoothDisjointUnionData (fun i => pieces (e i)) C where
  region i := U.region (e i)
  region_open i := U.region_open (e i)
  region_closed i := U.region_closed (e i)
  identify i := U.identify (e i)
  pairwise_disjoint i j hij := U.pairwise_disjoint (e i) (e j)
    (fun h => hij (e.injective h))
  cover := (e.surjective.iUnion_comp U.region).trans U.cover

def SmoothFiniteConnectedSumAssembly.reindexM38 {m : Nat}
    (S : SmoothFiniteConnectedSumAssembly pieces C) (e : Equiv (Fin m) (Fin n)) :
    SmoothFiniteConnectedSumAssembly (fun i => pieces (e i)) C where
  initial := S.initial
  disjoint_union := S.disjoint_union.reindexM38 e
  operations := S.operations

theorem smoothConnectedSumChain_of_finset_erase
    {iota : Type v} [DecidableEq iota]
    (stage : Finset iota -> GeneralizedSliceCarrier.{u}) (cuts : Finset iota)
    (next : ∀ s ⊆ cuts, s.Nonempty ->
      ∃ i ∈ s,
        SmoothConnectedSumStep (stage s) (stage (s.erase i))) :
    Relation.ReflTransGen SmoothConnectedSumStep (stage cuts) (stage ∅) := by
  have aux : ∀ s : Finset iota, s ⊆ cuts ->
      Relation.ReflTransGen SmoothConnectedSumStep (stage s) (stage ∅) := by
    intro s
    refine Finset.strongInductionOn s ?_
    intro t ih ht
    rcases t.eq_empty_or_nonempty with rfl | hnonempty
    · exact Relation.ReflTransGen.refl
    · obtain ⟨i, hi, hstep⟩ := next t ht hnonempty
      exact Relation.ReflTransGen.head hstep
        (ih (t.erase i) (Finset.erase_ssubset hi) ((Finset.erase_subset i t).trans ht))
  exact aux cuts le_rfl

def SmoothDisjointUnionData.assembleFinsetErasing
    {iota : Type v} [DecidableEq iota]
    (stage : Finset iota -> GeneralizedSliceCarrier.{u}) (cuts : Finset iota)
    (U : SmoothDisjointUnionData pieces (stage cuts))
    (next : ∀ s ⊆ cuts, s.Nonempty ->
      ∃ i ∈ s,
        SmoothConnectedSumStep (stage s) (stage (s.erase i))) :
    SmoothFiniteConnectedSumAssembly pieces (stage ∅) :=
  U.toAssembly.trans (smoothConnectedSumChain_of_finset_erase stage cuts next)

def SmoothFiniteConnectedSumAssembly.transFinsetErasing
    {iota : Type v} [DecidableEq iota]
    (stage : Finset iota -> GeneralizedSliceCarrier.{u}) (cuts : Finset iota)
    (S : SmoothFiniteConnectedSumAssembly pieces (stage cuts))
    (next : ∀ s ⊆ cuts, s.Nonempty ->
      ∃ i ∈ s,
        SmoothConnectedSumStep (stage s) (stage (s.erase i))) :
    SmoothFiniteConnectedSumAssembly pieces (stage ∅) :=
  S.trans (smoothConnectedSumChain_of_finset_erase stage cuts next)

theorem smoothConnectedSumChain_of_finite_set
    {iota : Type v} (stage : Set iota -> GeneralizedSliceCarrier.{u})
    (cuts : Set iota) (hfinite : cuts.Finite)
    (next : ∀ s ⊆ cuts, s.Nonempty ->
      ∃ i ∈ s, SmoothConnectedSumStep (stage s) (stage (s \ {i}))) :
    Relation.ReflTransGen SmoothConnectedSumStep (stage cuts) (stage ∅) := by
  classical
  have hchain := smoothConnectedSumChain_of_finset_erase
    (fun s : Finset iota => stage (s : Set iota)) hfinite.toFinset (by
      intro s hs hnonempty
      have hsubset : (s : Set iota) ⊆ cuts :=
        Set.Finite.subset_toFinset.mp hs
      obtain ⟨i, hi, hstep⟩ := next (s : Set iota) hsubset hnonempty.to_set
      exact ⟨i, hi, by simpa only [Finset.coe_erase] using hstep⟩)
  simpa only [Set.Finite.coe_toFinset, Finset.coe_empty] using hchain

def SmoothDisjointUnionData.assembleFiniteSet
    {iota : Type v} (stage : Set iota -> GeneralizedSliceCarrier.{u})
    (cuts : Set iota) (hfinite : cuts.Finite)
    (U : SmoothDisjointUnionData pieces (stage cuts))
    (next : ∀ s ⊆ cuts, s.Nonempty ->
      ∃ i ∈ s, SmoothConnectedSumStep (stage s) (stage (s \ {i}))) :
    SmoothFiniteConnectedSumAssembly pieces (stage ∅) :=
  U.toAssembly.trans (smoothConnectedSumChain_of_finite_set stage cuts hfinite next)

def SmoothFiniteConnectedSumAssembly.transFiniteSet
    {iota : Type v} (stage : Set iota -> GeneralizedSliceCarrier.{u})
    (cuts : Set iota) (hfinite : cuts.Finite)
    (S : SmoothFiniteConnectedSumAssembly pieces (stage cuts))
    (next : ∀ s ⊆ cuts, s.Nonempty ->
      ∃ i ∈ s, SmoothConnectedSumStep (stage s) (stage (s \ {i}))) :
    SmoothFiniteConnectedSumAssembly pieces (stage ∅) :=
  S.trans (smoothConnectedSumChain_of_finite_set stage cuts hfinite next)

end PoincareConjecture
