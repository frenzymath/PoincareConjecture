import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SourceStripClosing

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)




theorem source_strip_fibers_of_signed_tube
    {E F : Type*} (sigma : P2 × ℝ → E) {a b : ℝ}
    (closing : SignedAxisPermutation)
    (hfib : ∀ x y : ↥(signedTubeDiamond ×ˢ Icc a b),
      sigma x = sigma y ↔ x = y ∨
        ((x : P2 × ℝ).2 = a ∧ (y : P2 × ℝ).2 = b ∧
          closing.linear (x : P2 × ℝ).1 = (y : P2 × ℝ).1) ∨
        ((y : P2 × ℝ).2 = a ∧ (x : P2 × ℝ).2 = b ∧
          closing.linear (y : P2 × ℝ).1 = (x : P2 × ℝ).1))
    (phi : Fin 2 → P2 → F) (graph : F → E)
    (hgraph : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      graph (phi j z) = sigma (signedSheetStripMap j z))
    (hsep : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b → phi j z ≠ phi j.rev z)
    (hclose : ∀ j u, u ∈ Icc (-1 : ℝ) 1 →
      phi j (u, a) = phi (closing.index j) ((if closing.sign j.rev then u else -u), b)) :
    ∀ j k z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      ∀ w, w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      (phi j z = phi k w ↔
        (j = k ∧ z = w) ∨
        (z.2 = a ∧ w.2 = b ∧ k = closing.index j ∧
          w.1 = (if closing.sign j.rev then z.1 else -z.1)) ∨
        (w.2 = a ∧ z.2 = b ∧ j = closing.index k ∧
          z.1 = (if closing.sign k.rev then w.1 else -w.1))) := by
  have hindex (j k : Fin 2) (z : P2) (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
      (heq : phi j z = phi k z) : j = k := by
    by_contra hne
    have hk : k = j.rev := by fin_cases j <;> fin_cases k <;> simp_all [Fin.rev]
    exact hsep j z hz (hk ▸ heq)
  have hwrap (j k : Fin 2) (z w : P2)
      (hw : w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b) (hza : z.2 = a) (hwb : w.2 = b)
      (hc : closing.linear (signedSheetStripMap j z).1 = (signedSheetStripMap k w).1)
      (heq : phi j z = phi k w) :
      k = closing.index j ∧ w.1 = (if closing.sign j.rev then z.1 else -z.1) := by
    have hcoords : closing.linear (signedSheetStripMap j (z.1, 0)).1 =
        (signedSheetStripMap k (w.1, 0)).1 := by
      simpa only [signedSheetStripMap_apply] using hc
    rcases (signed_sheet_coordinate_eq_iff closing j k z.1 w.1).mp hcoords with h | h
    · exact h
    · have hzform : z = (0, a) := Prod.ext h.1 hza
      have hwform : w = (0, b) := Prod.ext h.2 hwb
      rw [hzform, hwform] at heq
      have hc0 : phi j (0, a) = phi (closing.index j) (0, b) := by
        simpa using hclose j 0 (by norm_num)
      have hind := hindex (closing.index j) k (0, b) (hwform ▸ hw) (hc0.symm.trans heq)
      exact ⟨hind.symm, by rw [h.1, h.2]; simp⟩
  intro j k z hz w hw
  constructor
  · intro heq
    have heq' := (hgraph j z hz).symm.trans ((congrArg graph heq).trans (hgraph k w hw))
    rcases (hfib ⟨_, signedSheetStripMap_mem j hz⟩
      ⟨_, signedSheetStripMap_mem k hw⟩).mp heq' with h | h | h
    · have hv := congrArg Subtype.val h
      have htime : z.2 = w.2 := by simpa only [signedSheetStripMap_apply] using congrArg Prod.snd hv
      have hcoords : SignedAxisPermutation.refl.linear (signedSheetStripMap j (z.1, 0)).1 =
          (signedSheetStripMap k (w.1, 0)).1 := by
        simpa [SignedAxisPermutation.linear_apply, SignedAxisPermutation.refl,
          signedSheetStripMap_apply] using congrArg Prod.fst hv
      have hh := (signed_sheet_coordinate_eq_iff SignedAxisPermutation.refl j k z.1 w.1).mp hcoords
      simp only [SignedAxisPermutation.refl, SignedAxisPermutation.index, jointSheetIndex,
        Bool.false_eq_true, if_false, if_true] at hh
      rcases hh with ⟨hkj, hcoord⟩ | ⟨hz0, hw0⟩
      · exact Or.inl ⟨hkj.symm, Prod.ext hcoord.symm htime⟩
      · have hzw : z = w := Prod.ext (hz0.trans hw0.symm) htime
        exact Or.inl ⟨hindex j k z hz (hzw.symm ▸ heq), hzw⟩
    · have hza : z.2 = a := by simpa only [signedSheetStripMap_apply] using h.1
      have hwb : w.2 = b := by simpa only [signedSheetStripMap_apply] using h.2.1
      exact Or.inr (Or.inl ⟨hza, hwb, hwrap j k z w hw hza hwb h.2.2 heq⟩)
    · have hwa : w.2 = a := by simpa only [signedSheetStripMap_apply] using h.1
      have hzb : z.2 = b := by simpa only [signedSheetStripMap_apply] using h.2.1
      exact Or.inr (Or.inr ⟨hwa, hzb, hwrap k j w z hz hwa hzb h.2.2 heq.symm⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨hza, hwb, rfl, hcoord⟩ | ⟨hwa, hzb, rfl, hcoord⟩)
    · rfl
    · have hzform : z = (z.1, a) := Prod.ext rfl hza
      have hwform : w = ((if closing.sign j.rev then z.1 else -z.1), b) := Prod.ext hcoord hwb
      rw [hzform, hwform]
      exact hclose j z.1 hz.1
    · have hwform : w = (w.1, a) := Prod.ext rfl hwa
      have hzform : z = ((if closing.sign k.rev then w.1 else -w.1), b) := Prod.ext hcoord hzb
      rw [hzform, hwform]
      exact (hclose k w.1 hw.1).symm

end PoincareConjecture.M76.Dehn
