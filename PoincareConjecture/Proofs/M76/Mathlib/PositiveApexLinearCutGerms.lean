import PoincareConjecture.Proofs.M76.Mathlib.AffineCutEndpointSigns
import PoincareConjecture.Proofs.M76.Mathlib.AffineCutApexLinearGerms











set_option autoImplicit false

open Set AffineMap CoordinateHalfBoxes

namespace ContinuousAffineEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem exists_positive_apex_linear_germ_of_forward_tail
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (A : E →ₗ[ℝ] ℝ)
    {a b : E} (hab : a ≠ b) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hf0 : f 0 = lineMap a b t) {r : ℝ} (hr : 0 < r)
    (hforward : ∀ x ∈ box r, f x ∈ lineMap a b '' Icc t 1 →
      x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2)
    (hheight : ∀ x, A (f x) = x.1.1) {σ : ℝ}
    (hside : (a = 0 ∧ 0 < σ) ∨ (b = 0 ∧ σ < 0)) :
    ∃ (k : ℝ) (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)),
      k = σ / (-(f.symm 0).1.2) ∧ 0 < k ∧
      e (lineMap a b t) = ((0, σ), 0) ∧
      (∀ x : (ℝ × ℝ) × ℝ,
        e (f x) = ((x.1.1, k * (x.1.2 - (f.symm 0).1.2)), x.2)) ∧
      (∀ x : E, (e x).1.1 = A x) ∧
      ∀ t z : ℝ, e (f ((t, 0), z)) = ((t, σ), z) := by
  obtain ⟨_, halast, _, hblast, haleft, hbright, _⟩ :=
    f.original_endpoint_signs_of_forward_tail hab ht hf0 hr hforward
  have hapex : (f.symm 0).2 = 0 := by
    rcases hside with ⟨ha, _⟩ | ⟨hb, _⟩
    · simpa only [ha] using halast
    · simpa only [hb] using hblast
  have hsign : ((f.symm 0).1.2 < 0 ∧ 0 < σ) ∨
      (0 < (f.symm 0).1.2 ∧ σ < 0) := by
    rcases hside with ⟨ha, hσ⟩ | ⟨hb, hσ⟩
    · exact Or.inl ⟨by simpa only [ha] using haleft, hσ⟩
    · exact Or.inr ⟨by simpa only [hb] using hbright, hσ⟩
  have hs : (f.symm 0).1.2 ≠ 0 := by
    rcases hsign with ⟨h, _⟩ | ⟨h, _⟩
    · exact h.ne
    · exact h.ne'
  have hσ : σ ≠ 0 := by
    rcases hsign with ⟨_, h⟩ | ⟨_, h⟩
    · exact h.ne'
    · exact h.ne
  have hquot : 0 < σ / (-(f.symm 0).1.2) := by
    rcases hsign with ⟨hsign, hσsign⟩ | ⟨hsign, hσsign⟩
    · exact div_pos hσsign (neg_pos.mpr hsign)
    · exact div_pos_of_neg_of_neg hσsign (neg_lt_zero.mpr hsign)
  have hcut : lineMap a b t ≠ 0 := by
    intro h
    have hzero : f.symm (lineMap a b t) = 0 := by
      rw [← hf0, f.symm_apply_apply]
    rw [h] at hzero
    exact hs (congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2) hzero)
  obtain ⟨k, e, hk, _, hp, hformula, heheight, hlateral⟩ :=
    f.exists_apex_linear_height_cut_germ A hf0 hcut hheight hapex hσ
  refine ⟨k, e, hk, ?_, hp, hformula, heheight, hlateral⟩
  rw [hk]
  exact hquot

end ContinuousAffineEquiv

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}






theorem exists_positive_apex_linear_germ_of_oriented_cut
    (P : Polygon E (n + 3)) (hinj : Function.Injective P)
    (t : Fin (n + 3) → ℝ) (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (i : Fin (n + 3)) (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (hf0 : f 0 = P.edgeCut t i) {r : ℝ} (hr : 0 < r)
    (harc : ∀ x ∈ box r, f x ∈ P.cutArc t i ↔
      x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2)
    (A : E →ₗ[ℝ] ℝ) (hheight : ∀ x, A (f x) = x.1.1) {σ : ℝ}
    (hside : (P i = 0 ∧ 0 < σ) ∨ (P (finRotate (n + 3) i) = 0 ∧ σ < 0)) :
    ∃ (k : ℝ) (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)),
      k = σ / (-(f.symm 0).1.2) ∧ 0 < k ∧
      e (P.edgeCut t i) = ((0, σ), 0) ∧
      (∀ x : (ℝ × ℝ) × ℝ,
        e (f x) = ((x.1.1, k * (x.1.2 - (f.symm 0).1.2)), x.2)) ∧
      (∀ x : E, (e x).1.1 = A x) ∧
      ∀ t z : ℝ, e (f ((t, 0), z)) = ((t, σ), z) := by
  apply f.exists_positive_apex_linear_germ_of_forward_tail A
    (P.edge_endpoints_ne_of_injective hinj i) (ht i) hf0 hr ?_ hheight hside
  intro x hx htail
  exact (harc x hx).mp (Or.inl htail)

end Polygon
