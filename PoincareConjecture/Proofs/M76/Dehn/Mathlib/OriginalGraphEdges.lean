import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AcyclicEdgeChains
import PoincareConjecture.Proofs.M76.Mathlib.ComplexCycleLabels










set_option autoImplicit false

namespace Sym2

variable {ι : Type*} [DecidableEq ι]



theorem toFinset_injective : Function.Injective (toFinset : Sym2 ι → Finset ι) := by
  intro p q h
  apply Sym2.ext
  intro x
  rw [← mem_toFinset, ← mem_toFinset, h]

end Sym2

open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] (A : AbstractSimplicialComplex ι)



theorem exists_original_face_of_graph_edge (T : SimpleGraph ι) (hT : T ≤ A.edgeGraph)
    (q : T.edgeSet) :
    ∃ e : Edge A.toPreAbstractSimplicialComplex,
      e.val = q.val.toFinset ∧ edgeInGraph A.toPreAbstractSimplicialComplex T e := by
  rcases q with ⟨q, hq⟩
  induction q using Sym2.ind with
  | h u v =>
    have huv := T.mem_edgeSet.mp hq
    let e : Edge A.toPreAbstractSimplicialComplex :=
      ⟨{u, v}, (hT huv).2, Finset.card_pair huv.ne⟩
    refine ⟨e, ?_, u, v, huv, ?_⟩
    · exact Sym2.toFinset_mk_eq.symm
    · ext x
      simp only [e, Finset.mem_insert, Finset.mem_singleton]




noncomputable def originalGraphEdgeEquiv (T : SimpleGraph ι) (hT : T ≤ A.edgeGraph) :
    T.edgeSet ≃ {e : Edge A.toPreAbstractSimplicialComplex //
      edgeInGraph A.toPreAbstractSimplicialComplex T e} := by
  classical
  choose f hface hmark using A.exists_original_face_of_graph_edge T hT
  let j : T.edgeSet → {e : Edge A.toPreAbstractSimplicialComplex //
      edgeInGraph A.toPreAbstractSimplicialComplex T e} := fun q => ⟨f q, hmark q⟩
  apply Equiv.ofBijective j
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Sym2.toFinset_injective
    have h := congrArg (fun e : {e : Edge A.toPreAbstractSimplicialComplex //
      edgeInGraph A.toPreAbstractSimplicialComplex T e} => e.val.val) hpq
    change (f p).val = (f q).val at h
    rwa [hface p, hface q] at h
  · intro e
    obtain ⟨u, v, huv, he⟩ := e.property
    let q : T.edgeSet := ⟨s(u, v), T.mem_edgeSet.mpr huv⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (f q).val = e.val.val
    rw [hface q]
    ext x
    rw [he]
    simp only [q, Sym2.mem_toFinset, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]



theorem card_original_graph_edges (T : SimpleGraph ι) (hT : T ≤ A.edgeGraph) :
    Nat.card T.edgeSet = Nat.card {e : Edge A.toPreAbstractSimplicialComplex //
      edgeInGraph A.toPreAbstractSimplicialComplex T e} :=
  Nat.card_congr (A.originalGraphEdgeEquiv T hT)

end AbstractSimplicialComplex
