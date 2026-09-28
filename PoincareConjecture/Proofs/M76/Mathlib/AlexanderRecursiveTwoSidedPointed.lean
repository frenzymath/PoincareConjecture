import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursivePointedCompletion
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveNegativeSuccessor
import PoincareConjecture.Proofs.M76.Mathlib.FixedNegativeCutHeightSigns










set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem AlexanderCollarSlab.exists_pointed_capped_deformation_with_two_sided_successor_and_signs
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab S A q β) (Mneg : AlexanderCollarSlab S (-A) q γ)
    {n : ℕ} (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hqP : q ∈ P.boundary ℝ) {d s₀ s₁ U : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ (P.boundary ℝ))
    (hs₁ : IsFinitePLBallPair (ℝ × ℝ) s₁ (P.boundary ℝ))
    (hunion : s₀ ∪ s₁ = S) (hinter : s₀ ∩ s₁ = P.boundary ℝ)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ S = P.boundary ℝ)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hsection : S ∩ {x | A x = 0} = P.boundary ℝ ∪ N.space)
    (hdN : d ∩ N.space ⊆ {q}) (hU : IsOpen U) (hdU : d ⊆ U)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ s s' : Set E, ((s = s₀ ∧ s' = s₁) ∨ (s = s₁ ∧ s' = s₀)) ∧
      IsFinitePLBallPair (ℝ × ℝ) s (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s' (P.boundary ℝ) ∧
      s ∪ s' = S ∧ s ∩ s' = P.boundary ℝ ∧
      d ∩ closure ((s ∪ d) ∩ {x | A x < 0}) ⊆ {q} ∧
      P.boundary ℝ \ {q} ⊆ closure ((s ∪ d) ∩ {x | 0 < A x}) ∧
      ∃ H : E ≃ₜ E,
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H : E → E) L.space) ∧
        FinitePiecewiseAffineOn (H : E → E) (s ∪ d) ∧
        IsFinitePLBallPair (ℝ × ℝ) (H '' d) (H '' P.boundary ℝ) ∧
        (∀ x ∈ M.residual, H x = x) ∧
        (∀ x ∈ (s ∪ d) ∩ {x | A x < 0}, H x = x) ∧
        (∀ x, x ∉ U → H x = x) ∧
        (∀ x, δ ≤ |A x| → H x = x) ∧
        (∀ x, β ≤ A x → H x = x) ∧
        (∀ x, A x ≤ A (H x)) ∧
        ((H '' (s ∪ d)) ∩ {x | A x = 0} =
          (((s ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q})) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) A q β) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-A) q γ) ∧
        ((∀ x ∈ S, A x ∈ Ioo (-γ) β → A x ≠ 0 →
            x ∈ closure (S ∩ {y | A y < A x}) ∧
              x ∈ closure (S ∩ {y | A x < A y})) →
          ∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) ∧
        ∀ c : ℝ, c ≠ 0 →
          ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
              ((H '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL ∧
            ∀ x : ((M.residual ∩ s) ∩ {x | A x = c} : Set E),
              ∃ y : (s ∩ {x | A x = c} : Set E), (y : E) = x ∧ (F y : E) = x := by
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
      H, hglobal, hPL, hball, hfixR, hneg, hfixU, hfixSlab, hhigh,
      hraise, hzero, hsuccessor, hpositiveSigns, hlevels⟩ :=
    M.exists_pointed_capped_deformation_with_successor_and_signs P hPe hPi hqP hd hs₀ hs₁
      hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ
  have hnegative := Mneg.nonempty_fixed_negative_successor P hPe hPi hqP hd hs hs'
    hss hssinter hdplane hcap N hN hsection hdN hside H hraise hneg hzero
  have hsigns (hsource : ∀ x ∈ S, A x ∈ Ioo (-γ) β → A x ≠ 0 →
      x ∈ closure (S ∩ {y | A y < A x}) ∧ x ∈ closure (S ∩ {y | A x < A y})) :
      ∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 →
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
          x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
    intro x hx hxA hxzero
    rcases lt_or_gt_of_ne hxzero with hxneg | hxpos
    · obtain ⟨y, hy, hyx⟩ := hx
      have hyA : A y < 0 := (hraise y).trans_lt (by simpa only [hyx] using hxneg)
      have hys : y ∈ s := by
        rcases hy with hys | hyd
        · exact hys
        · exact (hyA.ne (hdplane hyd)).elim
      have hxy : x = y := hyx.symm.trans (hneg y ⟨Or.inl hys, hyA⟩)
      have hxs : x ∈ s := hxy.symm ▸ hys
      obtain ⟨hlo, hhi⟩ := hsource x (hss.subset (Or.inl hxs)) hxA hxzero
      exact H.mem_both_height_closures_of_fixed_negative_cut A
        A.continuous_of_finiteDimensional hs'.isCompact.isClosed hss
        (hssinter.subset.trans (hd.1.trans hdplane))
        (fun y hy hyA => hneg y ⟨Or.inl hy, hyA⟩) hxs hxneg hlo hhi
    · exact hpositiveSigns (fun y hy hyA => hsource y hy
        ⟨(neg_lt_zero.mpr Mneg.width_pos).trans hyA.1, hyA.2⟩ hyA.1.ne')
        x hx ⟨hxpos, hxA.2⟩
  exact ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
    H, hglobal, hPL, hball, hfixR, hneg, hfixU, hfixSlab, hhigh,
    hraise, hzero, hsuccessor, hnegative, hsigns, hlevels⟩




theorem AlexanderCollarSlab.exists_pointed_capped_deformation_with_two_sided_successor
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab S A q β) (Mneg : AlexanderCollarSlab S (-A) q γ)
    {n : ℕ} (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hqP : q ∈ P.boundary ℝ) {d s₀ s₁ U : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ (P.boundary ℝ))
    (hs₁ : IsFinitePLBallPair (ℝ × ℝ) s₁ (P.boundary ℝ))
    (hunion : s₀ ∪ s₁ = S) (hinter : s₀ ∩ s₁ = P.boundary ℝ)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ S = P.boundary ℝ)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hsection : S ∩ {x | A x = 0} = P.boundary ℝ ∪ N.space)
    (hdN : d ∩ N.space ⊆ {q}) (hU : IsOpen U) (hdU : d ⊆ U)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ s s' : Set E, ((s = s₀ ∧ s' = s₁) ∨ (s = s₁ ∧ s' = s₀)) ∧
      IsFinitePLBallPair (ℝ × ℝ) s (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s' (P.boundary ℝ) ∧
      s ∪ s' = S ∧ s ∩ s' = P.boundary ℝ ∧
      d ∩ closure ((s ∪ d) ∩ {x | A x < 0}) ⊆ {q} ∧
      P.boundary ℝ \ {q} ⊆ closure ((s ∪ d) ∩ {x | 0 < A x}) ∧
      ∃ H : E ≃ₜ E,
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H : E → E) L.space) ∧
        FinitePiecewiseAffineOn (H : E → E) (s ∪ d) ∧
        IsFinitePLBallPair (ℝ × ℝ) (H '' d) (H '' P.boundary ℝ) ∧
        (∀ x ∈ M.residual, H x = x) ∧
        (∀ x ∈ (s ∪ d) ∩ {x | A x < 0}, H x = x) ∧
        (∀ x, x ∉ U → H x = x) ∧
        (∀ x, δ ≤ |A x| → H x = x) ∧
        (∀ x, β ≤ A x → H x = x) ∧
        (∀ x, A x ≤ A (H x)) ∧
        ((H '' (s ∪ d)) ∩ {x | A x = 0} =
          (((s ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q})) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) A q β) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-A) q γ) ∧
        ∀ c : ℝ, c ≠ 0 →
          ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
              ((H '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL ∧
            ∀ x : ((M.residual ∩ s) ∩ {x | A x = c} : Set E),
              ∃ y : (s ∩ {x | A x = c} : Set E), (y : E) = x ∧ (F y : E) = x := by
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
      H, hglobal, hPL, hball, hfixR, hneg, hfixU, hfixSlab, hhigh,
      hraise, hzero, hsuccessor, hnegative, _, hlevels⟩ :=
    M.exists_pointed_capped_deformation_with_two_sided_successor_and_signs Mneg
      P hPe hPi hqP hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ
  exact ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
    H, hglobal, hPL, hball, hfixR, hneg, hfixU, hfixSlab, hhigh,
    hraise, hzero, hsuccessor, hnegative, hlevels⟩

end Geometry
