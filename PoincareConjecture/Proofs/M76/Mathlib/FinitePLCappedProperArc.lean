import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProperArcExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedGraph










set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]





theorem exists_finitePL_capped_proper_arc_map
    {C p n q w : Set E} {D P N Q W : Set F} {a b : E} {A B : F}
    (hp : IsFinitePLBallPair (ℝ × ℝ) p q)
    (hn : IsFinitePLBallPair (ℝ × ℝ) n q)
    (hP : IsFinitePLBallPair (ℝ × ℝ) P Q)
    (hN : IsFinitePLBallPair (ℝ × ℝ) N Q)
    (hc : p ∪ n = frontier C) (hC : p ∩ n = q)
    (hd : P ∪ N = frontier D) (hD : P ∩ N = Q)
    (hw : IsFinitePLBallPair ℝ w {a, b})
    (hW : IsFinitePLBallPair ℝ W {A, B})
    (hab : a ≠ b) (hAB : A ≠ B)
    (ha : a ∈ q) (hb : b ∈ q) (hA : A ∈ Q) (hB : B ∈ Q)
    (hproper : w \ {a, b} ⊆ p \ q)
    (hProper : W \ {A, B} ⊆ P \ Q) :
    ∃ e : frontier C ≃ₜ frontier D, e.IsFinitePL ∧
      (∀ x : frontier C, (x : E) ∈ p ↔ (e x : F) ∈ P) ∧
      (∀ x : frontier C, (x : E) ∈ n ↔ (e x : F) ∈ N) ∧
      ∀ x : frontier C, (x : E) ∈ w ↔ (e x : F) ∈ W := by
  obtain ⟨ew, hew, hewa, hewb⟩ := hw.exists_marked_interval_homeomorph hW hab hAB
  have hends (x : w) : (x : E) ∈ ({a, b} : Set E) ↔
      (ew x : F) ∈ ({A, B} : Set F) := by
    simp only [mem_insert_iff, mem_singleton_iff, hewa, hewb]
  obtain ⟨ep, hep, _, hepw, hepq⟩ := hp.exists_extension_of_proper_arc hP hw hW
    hab hAB ha hb hA hB hproper hProper ew hew hends
  have hnp : n ∩ p = q := (inter_comm n p).trans hC
  have hNP : N ∩ P = Q := (inter_comm N P).trans hD
  obtain ⟨H, hH, hHp, hHn, hHpSet⟩ :=
    hn.exists_union_homeomorph_of_boundary_piece hN hnp hNP ep hep hepq
  have hnc : n ∪ p = frontier C := (union_comm n p).trans hc
  have hnd : N ∪ P = frontier D := (union_comm N P).trans hd
  let e := (Homeomorph.setCongr hnc.symm).trans
    (H.trans (Homeomorph.setCongr hnd))
  have hwp : w ⊆ p := by
    intro x hx
    by_cases hm : x ∈ ({a, b} : Set E)
    · exact hp.1 (hm.elim (fun h => h.symm ▸ ha) (fun h => h.symm ▸ hb))
    · exact (hproper ⟨hx, hm⟩).1
  have hWP : W ⊆ P := by
    intro x hx
    by_cases hm : x ∈ ({A, B} : Set F)
    · exact hP.1 (hm.elim (fun h => h.symm ▸ hA) (fun h => h.symm ▸ hB))
    · exact (hProper ⟨hx, hm⟩).1
  have hpval (x : p) :
      (e ⟨x, hc ▸ Or.inl x.property⟩ : F) = ep x :=
    congrArg (fun y : (N ∪ P : Set F) => (y : F)) (hHp x)
  have hpos (x : frontier C) : (x : E) ∈ p ↔ (e x : F) ∈ P :=
    hHpSet ⟨x, hnc.symm ▸ x.property⟩
  refine ⟨e, hH.setCongr hnc hnd, hpos,
    fun x => hHn ⟨x, hnc.symm ▸ x.property⟩, ?_⟩
  intro x
  constructor
  · intro hx
    have hxp := hwp hx
    have heq := hpval ⟨x, hxp⟩
    change (e x : F) = (ep ⟨x, hxp⟩ : F) at heq
    rw [heq]
    exact (hepw ⟨x, hxp⟩).mp hx
  · intro hx
    have hxp := (hpos x).mpr (hWP hx)
    have heq := hpval ⟨x, hxp⟩
    change (e x : F) = (ep ⟨x, hxp⟩ : F) at heq
    exact (hepw ⟨x, hxp⟩).mpr (heq ▸ hx)

end Set
