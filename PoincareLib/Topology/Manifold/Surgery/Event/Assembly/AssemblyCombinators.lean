import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.Topology

/-!
# Finite connected-sum assembly combinators

Morgan--Tian Proposition 15.3, printed pp. 357--358, reconstructs the
pre-surgery slice from a disjoint union by finitely many connected sums.
These combinators package supplied disjoint-union data and supplied steps
using the frozen Chapter 15 assembly type.
-/

set_option autoImplicit false

universe u v

namespace PoincareMT

variable {n : Nat} {pieces : Fin n -> GeneralizedSliceCarrier.{u}}
  {A C : GeneralizedSliceCarrier.{u}}

/-- A supplied disjoint union is an assembly with no connected-sum operations. -/
def SmoothDisjointUnionData.toAssembly (U : SmoothDisjointUnionData pieces C) :
    SmoothFiniteConnectedSumAssembly pieces C where
  initial := C
  disjoint_union := U
  operations := Relation.ReflTransGen.refl

/-- Append a supplied connected-sum step, keeping the initial disjoint union. -/
def SmoothFiniteConnectedSumAssembly.tail (S : SmoothFiniteConnectedSumAssembly pieces A)
    (h : SmoothConnectedSumStep A C) : SmoothFiniteConnectedSumAssembly pieces C where
  initial := S.initial
  disjoint_union := S.disjoint_union
  operations := Relation.ReflTransGen.tail S.operations h

/-- Append a supplied chain beginning at the assembly's current target. -/
def SmoothFiniteConnectedSumAssembly.trans (S : SmoothFiniteConnectedSumAssembly pieces A)
    (h : Relation.ReflTransGen SmoothConnectedSumStep A C) :
    SmoothFiniteConnectedSumAssembly pieces C where
  initial := S.initial
  disjoint_union := S.disjoint_union
  operations := Relation.ReflTransGen.trans S.operations h

/-- Reindex the supplied pieces bijectively, preserving their actual regions. -/
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

/-- Reindex only the initial disjoint union, keeping every operation unchanged. -/
def SmoothFiniteConnectedSumAssembly.reindexM38 {m : Nat}
    (S : SmoothFiniteConnectedSumAssembly pieces C) (e : Equiv (Fin m) (Fin n)) :
    SmoothFiniteConnectedSumAssembly (fun i => pieces (e i)) C where
  initial := S.initial
  disjoint_union := S.disjoint_union.reindexM38 e
  operations := S.operations

/-- If each nonempty subfamily has an actual reverse-cut step removing one
index, finitely many such steps reach the stage with no remaining indices.
This is the finite bookkeeping in Morgan--Tian Proposition 15.3, pp. 357--358;
the hypothesis must supply the geometry of every selected step. -/
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

/-- Start from the exact supplied disjoint union and undo a finite cut family. -/
def SmoothDisjointUnionData.assembleFinsetErasing
    {iota : Type v} [DecidableEq iota]
    (stage : Finset iota -> GeneralizedSliceCarrier.{u}) (cuts : Finset iota)
    (U : SmoothDisjointUnionData pieces (stage cuts))
    (next : ∀ s ⊆ cuts, s.Nonempty ->
      ∃ i ∈ s,
        SmoothConnectedSumStep (stage s) (stage (s.erase i))) :
    SmoothFiniteConnectedSumAssembly pieces (stage ∅) :=
  U.toAssembly.trans (smoothConnectedSumChain_of_finset_erase stage cuts next)

/-- Continue an assembly by supplied reverse-cut steps on a finite family. -/
def SmoothFiniteConnectedSumAssembly.transFinsetErasing
    {iota : Type v} [DecidableEq iota]
    (stage : Finset iota -> GeneralizedSliceCarrier.{u}) (cuts : Finset iota)
    (S : SmoothFiniteConnectedSumAssembly pieces (stage cuts))
    (next : ∀ s ⊆ cuts, s.Nonempty ->
      ∃ i ∈ s,
        SmoothConnectedSumStep (stage s) (stage (s.erase i))) :
    SmoothFiniteConnectedSumAssembly pieces (stage ∅) :=
  S.trans (smoothConnectedSumChain_of_finset_erase stage cuts next)

/-- The same reverse-cut chain for finite sets, matching set-indexed capped
carriers. Any cuts held fixed inside `stage` remain in the final `stage ∅`. -/
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

/-- Undo a finite set of supplied cuts from the literal initial disjoint union. -/
def SmoothDisjointUnionData.assembleFiniteSet
    {iota : Type v} (stage : Set iota -> GeneralizedSliceCarrier.{u})
    (cuts : Set iota) (hfinite : cuts.Finite)
    (U : SmoothDisjointUnionData pieces (stage cuts))
    (next : ∀ s ⊆ cuts, s.Nonempty ->
      ∃ i ∈ s, SmoothConnectedSumStep (stage s) (stage (s \ {i}))) :
    SmoothFiniteConnectedSumAssembly pieces (stage ∅) :=
  U.toAssembly.trans (smoothConnectedSumChain_of_finite_set stage cuts hfinite next)

/-- Append finite set-indexed reverse-cut operations to an existing assembly. -/
def SmoothFiniteConnectedSumAssembly.transFiniteSet
    {iota : Type v} (stage : Set iota -> GeneralizedSliceCarrier.{u})
    (cuts : Set iota) (hfinite : cuts.Finite)
    (S : SmoothFiniteConnectedSumAssembly pieces (stage cuts))
    (next : ∀ s ⊆ cuts, s.Nonempty ->
      ∃ i ∈ s, SmoothConnectedSumStep (stage s) (stage (s \ {i}))) :
    SmoothFiniteConnectedSumAssembly pieces (stage ∅) :=
  S.trans (smoothConnectedSumChain_of_finite_set stage cuts hfinite next)

end PoincareMT
