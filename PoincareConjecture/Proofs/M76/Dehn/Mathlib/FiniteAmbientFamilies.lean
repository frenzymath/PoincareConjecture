import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

open Set unitInterval

namespace Homeomorph

theorem exists_finite_family_history_composite
    {X V : Type*} [TopologicalSpace X] {n : ℕ}
    (G : Fin n → I → X ≃ₜ X)
    (hG : ∀ i, Continuous (fun z : I × X => G i z.1 z.2))
    (hGi : ∀ i, Continuous (fun z : I × X => (G i z.1).symm z.2))
    (hzero : ∀ i x, G i 0 x = x)
    {R F : Set X}
    (hR : ∀ i a, (G i a) ⁻¹' R = R)
    (hF : ∀ i a, (G i a) ⁻¹' F = F)
    (maps : ℕ → V → X)
    (hstep : ∀ i (hi : i < n), maps (i + 1) = G ⟨i, hi⟩ 1 ∘ maps i) :
    ∃ H : I → X ≃ₜ X,
      Continuous (fun z : I × X => H z.1 z.2) ∧
      Continuous (fun z : I × X => (H z.1).symm z.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ a, (H a) ⁻¹' R = R ∧ (H a) ⁻¹' F = F) ∧
      maps n = H 1 ∘ maps 0 := by
  classical
  let A (k : ℕ) (a : I) : X ≃ₜ X :=
    if hk : k < n then G ⟨k, hk⟩ a else Homeomorph.refl X
  have hAc (k : ℕ) : Continuous (fun z : I × X => A k z.1 z.2) := by
    by_cases hk : k < n
    · simpa only [A, dif_pos hk] using hG ⟨k, hk⟩
    · simpa only [A, dif_neg hk, Homeomorph.refl_apply, id_eq] using
        (continuous_snd : Continuous (fun z : I × X => z.2))
  have hAci (k : ℕ) : Continuous (fun z : I × X => (A k z.1).symm z.2) := by
    by_cases hk : k < n
    · simpa only [A, dif_pos hk] using hGi ⟨k, hk⟩
    · simpa only [A, dif_neg hk, Homeomorph.refl_symm, Homeomorph.refl_apply, id_eq] using
        (continuous_snd : Continuous (fun z : I × X => z.2))
  have hAzero (k : ℕ) (x : X) : A k 0 x = x := by
    by_cases hk : k < n
    · simpa only [A, dif_pos hk] using hzero ⟨k, hk⟩ x
    · simp only [A, dif_neg hk, Homeomorph.refl_apply, id_eq]
  have hAsets (k : ℕ) (a : I) : (A k a) ⁻¹' R = R ∧ (A k a) ⁻¹' F = F := by
    by_cases hk : k < n
    · simpa only [A, dif_pos hk] using And.intro (hR ⟨k, hk⟩ a) (hF ⟨k, hk⟩ a)
    · simp only [A, dif_neg hk, Homeomorph.refl_apply, preimage_id, and_self]
  let H : ℕ → I → X ≃ₜ X := Nat.rec (fun _ => Homeomorph.refl X)
    (fun k prev a => (prev a).trans (A k a))
  have hH (k : ℕ) :
      Continuous (fun z : I × X => H k z.1 z.2) ∧
      Continuous (fun z : I × X => (H k z.1).symm z.2) ∧
      (∀ x, H k 0 x = x) ∧
      ∀ a, (H k a) ⁻¹' R = R ∧ (H k a) ⁻¹' F = F := by
    induction k with
    | zero =>
      exact ⟨continuous_snd, continuous_snd, fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
    | succ k ih =>
      refine ⟨(hAc k).comp (continuous_fst.prodMk ih.1),
        ih.2.1.comp (continuous_fst.prodMk (hAci k)), ?_, ?_⟩
      · intro x
        change A k 0 (H k 0 x) = x
        rw [ih.2.2.1, hAzero]
      · intro a
        change (H k a) ⁻¹' ((A k a) ⁻¹' R) = R ∧
          (H k a) ⁻¹' ((A k a) ⁻¹' F) = F
        rw [(hAsets k a).1, (hAsets k a).2]
        exact ih.2.2.2 a
  have hendpoint : ∀ k ≤ n, maps k = H k 1 ∘ maps 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      rfl
    | succ k ih =>
      intro hkn
      have hk : k < n := (Nat.lt_succ_self k).trans_le hkn
      rw [hstep k hk, ih ((Nat.le_succ k).trans hkn)]
      funext x
      change G ⟨k, hk⟩ 1 (H k 1 (maps 0 x)) = A k 1 (H k 1 (maps 0 x))
      simp only [A, dif_pos hk]
  exact ⟨H n, (hH n).1, (hH n).2.1, (hH n).2.2.1, (hH n).2.2.2,
    hendpoint n le_rfl⟩

end Homeomorph
