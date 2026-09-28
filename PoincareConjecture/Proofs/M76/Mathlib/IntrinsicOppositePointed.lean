import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveTwoSidedPointed

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AlexanderCollarSlab.exists_intrinsic_opposite_pointed_deformations_with_signs
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
      ∃ H G : E ≃ₜ E,
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H : E → E) L.space) ∧
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (G : E → E) L.space) ∧
        FinitePiecewiseAffineOn (H : E → E) (s ∪ d) ∧
        FinitePiecewiseAffineOn (G : E → E) (s' ∪ d) ∧
        IsFinitePLBallPair (ℝ × ℝ) (H '' d) (H '' P.boundary ℝ) ∧
        IsFinitePLBallPair (ℝ × ℝ) (G '' d) (G '' P.boundary ℝ) ∧
        (∀ x ∈ M.residual, H x = x) ∧ (∀ x ∈ Mneg.residual, G x = x) ∧
        (∀ x, x ∉ U → H x = x ∧ G x = x) ∧
        (∀ x, δ ≤ |A x| → H x = x ∧ G x = x) ∧
        (∀ x, A x ≤ A (H x) ∧ A (G x) ≤ A x) ∧
        ((H '' (s ∪ d)) ∩ {x | A x = 0} =
          (((s ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q})) ∧
        ((G '' (s' ∪ d)) ∩ {x | A x = 0} =
          (((s' ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q})) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) A q β) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-A) q γ) ∧
        Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) A q β) ∧
        Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) (-A) q γ) ∧
        ((∀ x ∈ S, A x ∈ Ioo (-γ) β → A x ≠ 0 →
            x ∈ closure (S ∩ {y | A y < A x}) ∧
              x ∈ closure (S ∩ {y | A x < A y})) →
          (∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) ∧
          (∀ x ∈ G '' (s' ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 →
            x ∈ closure ((G '' (s' ∪ d)) ∩ {y | A y < A x}) ∧
              x ∈ closure ((G '' (s' ∪ d)) ∩ {y | A x < A y}))) ∧
        ∀ c : ℝ, c ≠ 0 →
          (∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
            ((H '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL) ∧
          (∃ F : (s' ∩ {x | A x = c} : Set E) ≃ₜ
            ((G '' (s' ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL) := by
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, _, happroach,
      H, hglobalH, hPLH, hballH, hfixRH, _, hfixH, hslabH, _,
      hraiseH, hzeroH, hsuccessorH, hnegativeH, hsignsH, hlevelsH⟩ :=
    M.exists_pointed_capped_deformation_with_two_sided_successor_and_signs Mneg
      P hPe hPi hqP hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ
  have Mback : AlexanderCollarSlab S (-(-A)) q β := by simpa only [neg_neg] using M
  have hdplaneNeg : d ⊆ {x | (-A) x = 0} := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hdplane
  have hsectionNeg : S ∩ {x | (-A) x = 0} = P.boundary ℝ ∪ N.space := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hsection
  obtain ⟨r, _, hrlabels, _, _, _, _, hrside, _,
      G, hglobalG, hPLG, hballG, hfixRG, _, hfixG, hslabG, _,
      hraiseG, hzeroG, hsuccessorG, hnegativeG, hsignsG, hlevelsG⟩ :=
    Mneg.exists_pointed_capped_deformation_with_two_sided_successor_and_signs Mback
      P hPe hPi hqP hd hs₀ hs₁ hunion hinter hdplaneNeg hcap N hN hsectionNeg hdN hU hdU hδ
  have hrpositive : d ∩ closure ((r ∪ d) ∩ {x | 0 < A x}) ⊆ {q} := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_zero] using hrside
  have hsr : s ≠ r := by
    intro heq
    obtain ⟨ec⟩ := P.nonempty_boundary_homeomorph_circle hPe hPi
    obtain ⟨x, hxb, hxq⟩ :=
      (isConnected_sdiff_singleton_of_homeomorph_circle (P.boundary ℝ) ec q).nonempty
    have hxcl := happroach ⟨hxb, hxq⟩
    rw [heq] at hxcl
    exact hxq (hrpositive ⟨hd.1 hxb, hxcl⟩)
  have hrs' : r = s' := by
    rcases hlabels with ⟨hs, hs'⟩ | ⟨hs, hs'⟩
    · rcases hrlabels with ⟨hr, _⟩ | ⟨hr, _⟩
      · exact (hsr (hs.trans hr.symm)).elim
      · exact hr.trans hs'.symm
    · rcases hrlabels with ⟨hr, _⟩ | ⟨hr, _⟩
      · exact hr.trans hs'.symm
      · exact (hsr (hs.trans hr.symm)).elim
  subst r
  have hsigns (hsource : ∀ x ∈ S, A x ∈ Ioo (-γ) β → A x ≠ 0 →
      x ∈ closure (S ∩ {y | A y < A x}) ∧ x ∈ closure (S ∩ {y | A x < A y})) :
      (∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 →
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
          x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) ∧
      (∀ x ∈ G '' (s' ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 →
        x ∈ closure ((G '' (s' ∪ d)) ∩ {y | A y < A x}) ∧
          x ∈ closure ((G '' (s' ∪ d)) ∩ {y | A x < A y})) := by
    refine ⟨hsignsH hsource, ?_⟩
    have hsourceNeg : ∀ x ∈ S, (-A) x ∈ Ioo (-β) γ → (-A) x ≠ 0 →
        x ∈ closure (S ∩ {y | (-A) y < (-A) x}) ∧
          x ∈ closure (S ∩ {y | (-A) x < (-A) y}) := by
      intro x hx hxA hxzero
      have hxA' : A x ∈ Ioo (-γ) β := by
        change -β < -A x ∧ -A x < γ at hxA
        constructor <;> linarith [hxA.1, hxA.2]
      have hxzero' : A x ≠ 0 := by
        simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_ne_zero] using hxzero
      obtain ⟨hlo, hhi⟩ := hsource x hx hxA' hxzero'
      exact ⟨by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_neg_iff] using hhi,
        by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_neg_iff] using hlo⟩
    intro x hx hxA hxzero
    have hxA' : (-A) x ∈ Ioo (-β) γ := by
      change -β < -A x ∧ -A x < γ
      constructor <;> linarith [hxA.1, hxA.2]
    have hxzero' : (-A) x ≠ 0 := by
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_ne_zero] using hxzero
    obtain ⟨hlo, hhi⟩ := hsignsG hsourceNeg x hx hxA' hxzero'
    exact ⟨by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_neg_iff] using hhi,
      by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_neg_iff] using hlo⟩
  refine ⟨s, s', hlabels, hs, hs', hss, hssinter, H, G,
    hglobalH, hglobalG, hPLH, hPLG, hballH, hballG, hfixRH, hfixRG,
    (fun x hx => ⟨hfixH x hx, hfixG x hx⟩), ?_, ?_, hzeroH, ?_,
    hsuccessorH, hnegativeH, ?_, hsuccessorG, hsigns, fun c hc => ?_⟩
  · intro x hx
    exact ⟨hslabH x hx, hslabG x
      (by simpa only [AffineMap.coe_neg, Pi.neg_apply, abs_neg] using hx)⟩
  · intro x
    exact ⟨hraiseH x, by
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_le_neg_iff] using hraiseG x⟩
  · simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hzeroG
  · simpa only [neg_neg] using hnegativeG
  · obtain ⟨F, hF, _⟩ := hlevelsH c hc
    refine ⟨⟨F, hF⟩, ?_⟩
    obtain ⟨F', hF', _⟩ := hlevelsG (-c) (neg_ne_zero.mpr hc)
    have hlevel : {x : E | (-A) x = -c} = {x | A x = c} := by
      ext x
      change (-A x = -c) ↔ A x = c
      exact neg_inj
    have hsource := congrArg (s' ∩ ·) hlevel
    have htarget := congrArg ((G '' (s' ∪ d)) ∩ ·) hlevel
    exact ⟨(Homeomorph.setCongr hsource.symm).trans (F'.trans (Homeomorph.setCongr htarget)),
      hF'.setCongr hsource htarget⟩

theorem AlexanderCollarSlab.exists_intrinsic_opposite_pointed_deformations
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
      ∃ H G : E ≃ₜ E,
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H : E → E) L.space) ∧
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (G : E → E) L.space) ∧
        FinitePiecewiseAffineOn (H : E → E) (s ∪ d) ∧
        FinitePiecewiseAffineOn (G : E → E) (s' ∪ d) ∧
        IsFinitePLBallPair (ℝ × ℝ) (H '' d) (H '' P.boundary ℝ) ∧
        IsFinitePLBallPair (ℝ × ℝ) (G '' d) (G '' P.boundary ℝ) ∧
        (∀ x ∈ M.residual, H x = x) ∧ (∀ x ∈ Mneg.residual, G x = x) ∧
        (∀ x, x ∉ U → H x = x ∧ G x = x) ∧
        (∀ x, δ ≤ |A x| → H x = x ∧ G x = x) ∧
        (∀ x, A x ≤ A (H x) ∧ A (G x) ≤ A x) ∧
        ((H '' (s ∪ d)) ∩ {x | A x = 0} =
          (((s ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q})) ∧
        ((G '' (s' ∪ d)) ∩ {x | A x = 0} =
          (((s' ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q})) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) A q β) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-A) q γ) ∧
        Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) A q β) ∧
        Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) (-A) q γ) ∧
        ∀ c : ℝ, c ≠ 0 →
          (∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
            ((H '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL) ∧
          (∃ F : (s' ∩ {x | A x = c} : Set E) ≃ₜ
            ((G '' (s' ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL) := by
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, H, G,
      hglobalH, hglobalG, hPLH, hPLG, hballH, hballG, hfixRH, hfixRG,
      hfix, hslab, hraise, hzeroH, hzeroG, hpositiveH, hnegativeH,
      hpositiveG, hnegativeG, _, hlevels⟩ :=
    M.exists_intrinsic_opposite_pointed_deformations_with_signs Mneg
      P hPe hPi hqP hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ
  exact ⟨s, s', hlabels, hs, hs', hss, hssinter, H, G,
    hglobalH, hglobalG, hPLH, hPLG, hballH, hballG, hfixRH, hfixRG,
    hfix, hslab, hraise, hzeroH, hzeroG, hpositiveH, hnegativeH,
    hpositiveG, hnegativeG, hlevels⟩

end Geometry
