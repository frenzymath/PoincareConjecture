import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SignedAxisMonodromy

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem signed_axis_closing_classification {n : ℕ}
    (P : Polygon P2 (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) {r a b : ℝ} (hr : 0 < r) (hab : a < b)
    (phi : Fin 2 → P2 → P2)
    (hPL : ∀ j, FinitePiecewiseAffineOn (phi j) (Icc (-r) r ×ˢ Icc a b))
    (hinj : ∀ j, InjOn (phi j) (Ioo (-r) r ×ˢ Ioo a b))
    (haxis : ∀ j x, x ∈ Icc (-r) r ×ˢ Icc a b →
      (phi j x ∈ P.boundary ℝ ↔ x.1 = 0))
    (closing : SignedAxisPermutation)
    (hclose : ∀ (j : Fin 2) u, u ∈ Icc (-r) r →
      phi j (u, a) = phi (closing.index j)
        ((if closing.sign j.rev then u else -u), b)) :
    closing = SignedAxisPermutation.refl ∨
      (closing.swap = true ∧ closing.sign 0 = closing.sign 1) := by
  cases hs : closing.swap with
  | false =>
    have hsign (j : Fin 2) : closing.sign j.rev = true :=
      P.strip_closing_sign_eq_true hP hinjP hr hab (hPL j) (hinj j) (haxis j)
        (closing.sign j.rev)
        (by simpa [SignedAxisPermutation.index, jointSheetIndex, hs] using
          hclose j r ⟨by linarith, le_rfl⟩)
    refine Or.inl (SignedAxisPermutation.ext hs ?_)
    funext j
    simpa [SignedAxisPermutation.refl] using hsign j.rev
  | true =>
    refine Or.inr ⟨rfl, P.exchanged_strip_signs_eq hP hinjP hr hab
      phi hPL (hinj 0) haxis closing.sign ?_⟩
    intro j u hu
    simpa [SignedAxisPermutation.index, jointSheetIndex, hs] using hclose j u hu

theorem signed_axis_closing_eq_refl_of_planar_strips
    (n : Fin 2 → ℕ) (P : ∀ j, Polygon P2 (n j + 3))
    (hP : ∀ j, (P j).HasSimplicialEdges) (hinjP : ∀ j, Function.Injective (P j))
    {r a b : ℝ} (hr : 0 < r) (hab : a < b)
    (phi : Fin 2 → P2 → P2)
    (hPL : ∀ j, FinitePiecewiseAffineOn (phi j) (Icc (-r) r ×ˢ Icc a b))
    (hinj : ∀ j, InjOn (phi j) (Ioo (-r) r ×ˢ Ioo a b))
    (haxis : ∀ j x, x ∈ Icc (-r) r ×ˢ Icc a b →
      (phi j x ∈ (P j).boundary ℝ ↔ x.1 = 0))
    (closing : SignedAxisPermutation) (hswap : closing.swap = false)
    (hclose : ∀ (j : Fin 2) u, u ∈ Icc (-r) r →
      phi j (u, a) = phi (closing.index j)
        ((if closing.sign j.rev then u else -u), b)) :
    closing = SignedAxisPermutation.refl := by
  have hsign (j : Fin 2) : closing.sign j.rev = true :=
    (P j).strip_closing_sign_eq_true (hP j) (hinjP j) hr hab (hPL j) (hinj j) (haxis j)
      (closing.sign j.rev)
      (by simpa [SignedAxisPermutation.index, jointSheetIndex, hswap] using
        hclose j r ⟨by linarith, le_rfl⟩)
  refine SignedAxisPermutation.ext hswap ?_
  funext j
  simpa [SignedAxisPermutation.refl] using hsign j.rev

end PoincareConjecture.M76.Dehn.Annuli
