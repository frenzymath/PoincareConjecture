import PoincareConjecture.Proofs.M76.Dehn.Mathlib.DualFaceGraph

set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex

variable {V : Type*} [DecidableEq V] (A : AbstractSimplicialComplex V)
  (T : SimpleGraph V) (hT : T ≤ A.edgeGraph)

theorem mem_range_primalFaceLabel_iff (s : A.faces) :
    s ∈ Set.range (A.primalFaceLabel T hT) ↔ s.val.card = 1 ∨
      ∃ e : Edge A.toPreAbstractSimplicialComplex,
        edgeInGraph A.toPreAbstractSimplicialComplex T e ∧ s.val = e.val := by
  classical
  constructor
  · rintro ⟨x, rfl⟩
    rcases x with v | q
    · exact Or.inl (Finset.card_singleton v)
    · obtain ⟨e, he, hmark⟩ := A.exists_original_face_of_graph_edge T hT q
      exact Or.inr ⟨e, hmark, he.symm⟩
  · rintro (hcard | ⟨e, he, hs⟩)
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
      exact ⟨Sum.inl v, Subtype.ext hv.symm⟩
    · obtain ⟨u, v, huv, he⟩ := he
      refine ⟨Sum.inr ⟨s(u, v), T.mem_edgeSet.mpr huv⟩, Subtype.ext ?_⟩
      change (s(u, v)).toFinset = s.val
      rw [Sym2.toFinset_mk_eq, hs, he]
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]

variable [Fintype V]
  (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
    (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)

omit [DecidableEq V] in

theorem mem_range_dualFaceLabel_iff (s : A.faces) :
    s ∈ Set.range (dualFaceLabel A.toPreAbstractSimplicialComplex T hcofaces) ↔
      s.val.card = 3 ∨ ∃ e : Edge A.toPreAbstractSimplicialComplex,
        ¬edgeInGraph A.toPreAbstractSimplicialComplex T e ∧ s.val = e.val := by
  constructor
  · rintro ⟨x, rfl⟩
    rcases x with q | t
    · exact Or.inl q.property.2
    · exact Or.inr ⟨(complementaryTriangleEdgeEquiv
        A.toPreAbstractSimplicialComplex T hcofaces t).val,
        (complementaryTriangleEdgeEquiv
          A.toPreAbstractSimplicialComplex T hcofaces t).property, rfl⟩
  · rintro (hcard | ⟨e, he, hs⟩)
    · exact ⟨Sum.inl ⟨s.val, s.property, hcard⟩, rfl⟩
    · refine ⟨Sum.inr ((complementaryTriangleEdgeEquiv
        A.toPreAbstractSimplicialComplex T hcofaces).symm ⟨e, he⟩), Subtype.ext ?_⟩
      change ((complementaryTriangleEdgeEquiv A.toPreAbstractSimplicialComplex T hcofaces)
        ((complementaryTriangleEdgeEquiv A.toPreAbstractSimplicialComplex T hcofaces).symm
          ⟨e, he⟩)).val.val = s.val
      rw [Equiv.apply_symm_apply]
      exact hs.symm

theorem range_dualFaceLabel_eq_compl
    (hbound : ∀ s ∈ A.faces, s.card ≤ 3) :
    Set.range (dualFaceLabel A.toPreAbstractSimplicialComplex T hcofaces) =
      (Set.range (A.primalFaceLabel T hT))ᶜ := by
  classical
  ext s
  change s ∈ Set.range (dualFaceLabel A.toPreAbstractSimplicialComplex T hcofaces) ↔
    ¬s ∈ Set.range (A.primalFaceLabel T hT)
  rw [A.mem_range_dualFaceLabel_iff T hcofaces,
    A.mem_range_primalFaceLabel_iff T hT]
  constructor
  · rintro (hthree | ⟨e, he, hse⟩) (hone | ⟨f, hf, hsf⟩)
    · omega
    · have htwo : s.val.card = 2 := by rw [hsf]; exact f.property.2
      omega
    · have htwo : s.val.card = 2 := by rw [hse]; exact e.property.2
      omega
    · have hef : e = f := Subtype.ext (hse.symm.trans hsf)
      exact he (hef.symm ▸ hf)
  · intro hnot
    have hone : s.val.card ≠ 1 := fun h => hnot (Or.inl h)
    by_cases htwo : s.val.card = 2
    · let e : Edge A.toPreAbstractSimplicialComplex := ⟨s.val, s.property, htwo⟩
      refine Or.inr ⟨e, ?_, rfl⟩
      intro he
      exact hnot (Or.inr ⟨e, he, rfl⟩)
    · have hpos : 0 < s.val.card :=
        Finset.card_pos.mpr (A.isRelLowerSet_faces s.property).1
      have hle := hbound s.val s.property
      exact Or.inl (by omega)

end AbstractSimplicialComplex
