import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveOrdinaryCompletion
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveLowerSigns
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveTerminalSigns
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicOrdinaryLevels

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AlexanderCollarSlab.exists_ordinary_intrinsic_deformation_with_band_geometry
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab S A q β) (Mneg : AlexanderCollarSlab S (-A) q γ)
    (hregular : ∀ c ∈ Ioo (0 : ℝ) β,
      HasDisjointPolygonPresentation (S ∩ {x | A x = c}))
    (hsigns : ∀ x ∈ S, A x ∈ Ioo (0 : ℝ) β →
      x ∈ closure (S ∩ {y | A y < A x}) ∧
        x ∈ closure (S ∩ {y | A x < A y}))
    {n : ℕ} (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hqP : q ∉ P.boundary ℝ) {d s₀ s₁ U : Set E}
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
      ∃ t : ℝ, t ∈ Ioo 0 β ∧ ∃ p : E, p ∈ d \ P.boundary ℝ ∧
        ∃ H : E ≃ₜ E,
          (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
            FinitePiecewiseAffineOn (H : E → E) L.space) ∧
          FinitePiecewiseAffineOn (H : E → E) (s ∪ d) ∧
          IsFinitePLBallPair (ℝ × ℝ) (H '' d) (H '' P.boundary ℝ) ∧
          (∀ x ∈ M.residual, H x = x) ∧
          (∀ x ∈ (s ∪ d) ∩ {x | A x < 0}, H x = x) ∧
          (∀ x, β ≤ A x → H x = x) ∧
          (∀ x, x ∉ U → H x = x) ∧ (∀ x, δ ≤ |A x| → H x = x) ∧
          (∀ x, A x ≤ A (H x)) ∧
          ((H '' (s ∪ d)) ∩ {x | A x = 0} = (((s ∪ d) ∩ {x | A x = 0}) \ d)) ∧
          (q ∈ s →
            Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) A q β) ∧
            Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-A) q γ)) ∧
          ((H '' d) ∩ {x | A x = t * (2 / 3)} = {H p}) ∧
          (∀ c : ℝ, c < t * (2 / 3) ∨ t < c → (H '' d) ∩ {x | A x = c} = ∅) ∧
          (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
            IsFinitePLBallPair (ℝ × ℝ) ((H '' d) ∩ {x | A x ≤ t * a})
              ((H '' d) ∩ {x | A x = t * a})) ∧
          (∀ c : ℝ, c < 0 ∨ t ≤ c →
            ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
              ((H '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL) ∧
          (∀ c ∈ Ioo (0 : ℝ) t,
            HasAlexanderCurvePresentation ((H '' (s ∪ d)) ∩ {x | A x = c}) 0 ∧
              (c ≠ t * (2 / 3) →
                HasDisjointPolygonPresentation ((H '' (s ∪ d)) ∩ {x | A x = c}))) ∧
          (∀ a b : ℝ, t < a → b ≤ β →
            ∃ G : (s ∩ {x | A x ∈ Icc a b} : Set E) ≃ₜ
                ((H '' (s ∪ d)) ∩ {x | A x ∈ Icc a b} : Set E),
              G.IsFinitePL ∧ ∀ x, A (G x) = A x) ∧
          (∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (0 : ℝ) β → x ≠ H p →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) ∧
          ∃ TX TY : Set E, TX ⊆ M.collar ∧ TY ⊆ M.collar ∧ TX ⊆ s ∧ TY ⊆ s ∧
            M.collar ∩ s = TX ∪ TY ∧ Disjoint TX TY ∧ Disjoint d TX ∧
            (∀ w : {w : E × ℝ | w.1 ∈ S ∩ {x | A x = 0} ∧
                w.2 ∈ Icc 0 (M.upper w.1)},
              (M.chart w : E) ∈ TX ↔ (w : E × ℝ).1 ∈ N.space ∩ s) ∧
            (∀ w : {w : E × ℝ | w.1 ∈ S ∩ {x | A x = 0} ∧
                w.2 ∈ Icc 0 (M.upper w.1)},
              (M.chart w : E) ∈ TY ↔ (w : E × ℝ).1 ∈ P.boundary ℝ) ∧
            ∃ F : (TX ∪ (M.residual ∩ s) : Set E) ≃ₜ
                ((H '' TX) ∪ (M.residual ∩ s) : Set E), F.IsFinitePL ∧
              (∀ x : (TX ∪ (M.residual ∩ s) : Set E), A (F x) = A x) ∧
              (∀ x : (M.residual ∩ s : Set E), (F ⟨x, Or.inr x.property⟩ : E) = x) ∧
              (∀ x : (TX ∪ (M.residual ∩ s) : Set E),
                (x : E) ∈ TX ↔ (F x : E) ∈ H '' TX) ∧
              (∀ x : (TX ∪ (M.residual ∩ s) : Set E),
                (x : E) ∈ M.residual ∩ s ↔ (F x : E) ∈ M.residual ∩ s) ∧
              (∀ x ∈ P.boundary ℝ, t < M.upper x) ∧
              (∀ x ∈ TY, t ≤ A (H x)) ∧
              ∀ x ∈ TY, A (H x) = t → x ∈ P.boundary ℝ := by
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
      t, ht, p, hp, H, hglobal, hPL, hball, hfixR, hneg, hhigh, hfix, hslab,
      hraise, hzero, hsuccessor, hminimum, hempty, hdisks, hlevels, hlow,
      hterminal, hcapSigns, TX, TY, hTX, hTY, hXs, hYs, hsplit, hdisj, hdcap, hCX, hCY,
      F, hF, hFA, hFR, hFT, hFRmem, hroof, hmoved, hrigidity⟩ :=
    M.exists_ordinary_capped_deformation_with_band_geometry Mneg
      P hPe hPi hqP hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ
  have hcut : s ∩ s' ⊆ {x | A x = 0} :=
    hssinter.subset.trans (hd.1.trans hdplane)
  have hpositiveSigns (x : E) (hx : x ∈ H '' (s ∪ d))
      (hxA : A x ∈ Ioo (0 : ℝ) β) (hxne : x ≠ H p) :
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
    by_cases hxt : A x ≤ t
    · exact M.ordinary_lower_band_mem_both_height_closures hs'.isCompact.isClosed
        hss hcut hsplit hdisj P.isCompact_boundary.isClosed hCY H
        (fun y _ => hraise y) (fun y hy hyA => hneg y ⟨Or.inl hy, hyA⟩)
        hfixR ht.2 hroof hmoved (fun y hy heq => hd.1 (hrigidity y hy heq)) F hFA
        (fun y hy hyA => hsigns y hy ⟨hyA.1, hyA.2.trans_lt ht.2⟩)
        hcapSigns x hx ⟨hxA.1, hxt⟩ hxne
    · exact Homeomorph.mem_both_height_closures_of_ordinary_terminal_bands A
        hs'.isCompact.isClosed hss hcut ht.1 hterminal hsigns x hx
          ⟨lt_of_not_ge hxt, hxA.2⟩
  refine ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
    t, ht, p, hp, H, hglobal, hPL, hball, hfixR, hneg, hhigh, hfix, hslab,
    hraise, hzero, hsuccessor, hminimum, hempty, hdisks, hlevels, ?_,
    hterminal, hpositiveSigns, TX, TY, hTX, hTY, hXs, hYs, hsplit, hdisj, hdcap, hCX, hCY,
    F, hF, hFA, hFR, hFT, hFRmem, hroof, hmoved, hrigidity⟩
  exact ordinary_capped_low_level_presentations A.continuous_of_finiteDimensional
    hs.isCompact.isClosed hs'.isCompact.isClosed hss hcut P.isCompact_boundary ht.1 H p
    (fun c hc => hregular c ⟨hc.1, hc.2.trans ht.2⟩) hminimum hempty hdisks hlow

end Geometry
