import PoincareConjecture.Proofs.M07.Topology.Gluing.Separation
import Mathlib.Topology.Compactness.Compact










set_option autoImplicit false

open Set Topology

universe u

namespace Poincare.Gluing

variable {X : Type u} [TopologicalSpace X]



def twoPieceOverlap (e : OpenPartialHomeomorph X X) (he : e.symm = e) :
    OverlapSystem (fun _ : Bool => X) where
  transition i j := if i = j then OpenPartialHomeomorph.refl X else e
  self i := if_pos rfl
  inverse i j := by
    by_cases h : i = j
    · subst j
      simp
    · simp only [if_neg h, if_neg (Ne.symm h), he]
  comp_source i j k x hx hy := by
    cases i <;> cases j <;> cases k <;>
      simp_all only [Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true,
        if_pos, if_neg, OpenPartialHomeomorph.refl_source, mem_univ,
        OpenPartialHomeomorph.refl_apply, id_eq]
  comp_apply i j k x hx hy := by
    cases i <;> cases j <;> cases k <;>
      simp_all only [Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true,
        if_pos, if_neg, OpenPartialHomeomorph.refl_apply,
        OpenPartialHomeomorph.refl_source, mem_univ, id_eq]
    all_goals simpa only [he] using e.left_inv hx



theorem twoPieceOverlap_transition_ne (e : OpenPartialHomeomorph X X)
    (he : e.symm = e) {i j : Bool} (hij : i ≠ j) :
    (twoPieceOverlap e he).transition i j = e := if_neg hij



theorem twoPieceOverlap_closed [T2Space X] (e : OpenPartialHomeomorph X X)
    (he : e.symm = e)
    (hgraph : IsClosed {p : X × X | p.1 ∈ e.source ∧ e p.1 = p.2}) :
    ∀ i j, IsClosed {p : X × X | (twoPieceOverlap e he).Rel ⟨i, p.1⟩ ⟨j, p.2⟩} := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa only [OverlapSystem.Rel, OverlapSystem.self,
      OpenPartialHomeomorph.refl_source, mem_univ, true_and,
      OpenPartialHomeomorph.refl_apply, id_eq] using
      (isClosed_eq continuous_fst continuous_snd : IsClosed {p : X × X | p.1 = p.2})
  · simpa only [OverlapSystem.Rel, twoPieceOverlap_transition_ne e he hij] using hgraph



theorem twoPieceOverlap_compactSpace (e : OpenPartialHomeomorph X X)
    (he : e.symm = e) {K : Set X} (hK : IsCompact K)
    (hcover : ∀ x : X, x ∈ K ∨ x ∈ e.source ∧ e x ∈ K) :
    CompactSpace (Quotient (twoPieceOverlap e he).setoid) := by
  let D := twoPieceOverlap e he
  have hc := (hK.image (D.include_isOpenEmbedding false).continuous).union
    (hK.image (D.include_isOpenEmbedding true).continuous)
  have hfull : D.include false '' K ∪ D.include true '' K = univ := by
    apply eq_univ_of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      rcases a with ⟨i, x⟩
      change D.include i x ∈ _
      rcases hcover x with hx | ⟨hx, hex⟩
      · cases i
        · exact Or.inl ⟨x, hx, rfl⟩
        · exact Or.inr ⟨x, hx, rfl⟩
      · have heq : D.include i x = D.include (!i) (e x) := by
          apply (D.include_eq_iff i (!i) x (e x)).mpr
          have hne : i ≠ !i := by cases i <;> decide
          rw [show D.transition i (!i) = e from twoPieceOverlap_transition_ne e he hne]
          exact ⟨hx, rfl⟩
        rw [heq]
        cases i
        · exact Or.inr ⟨e x, hex, rfl⟩
        · exact Or.inl ⟨e x, hex, rfl⟩
  exact ⟨hfull ▸ hc⟩

end Poincare.Gluing
