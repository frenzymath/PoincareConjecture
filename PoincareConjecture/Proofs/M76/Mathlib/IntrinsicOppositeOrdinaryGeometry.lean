import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicOrdinaryGeometry
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicOrdinaryAlternatives
import PoincareConjecture.Proofs.M76.Mathlib.RaisingCappedHeightSigns

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AlexanderCollarSlab.exists_intrinsic_opposite_ordinary_deformations_with_signs
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab S A q β) (Mneg : AlexanderCollarSlab S (-A) q γ)
    (hregular : ∀ c ∈ Ioo (0 : ℝ) β,
      HasDisjointPolygonPresentation (S ∩ {x | A x = c}))
    (hregularNeg : ∀ c ∈ Ioo (0 : ℝ) γ,
      HasDisjointPolygonPresentation (S ∩ {x | (-A) x = c}))
    (hsource : ∀ x ∈ S, A x ∈ Ioo (-γ) β → A x ≠ 0 →
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
        (∀ x ∈ s, A x < 0 → H x = x) ∧
        (∀ x ∈ s', 0 < A x → G x = x) ∧
        (∀ x, A x ≤ A (H x) ∧ A (G x) ≤ A x) ∧
        ((H '' (s ∪ d)) ∩ {x | A x = 0} = (((s ∪ d) ∩ {x | A x = 0}) \ d)) ∧
        ((G '' (s' ∪ d)) ∩ {x | A x = 0} = (((s' ∪ d) ∩ {x | A x = 0}) \ d)) ∧
        (q ∈ s →
          Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) A q β) ∧
          Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-A) q γ)) ∧
        (q ∈ s' →
          Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) A q β) ∧
          Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) (-A) q γ)) ∧
        (∃ t : ℝ, t ∈ Ioo 0 β ∧ ∃ p : E, p ∈ d \ P.boundary ℝ ∧
          (H '' d) ∩ {x | A x = t * (2 / 3)} = {H p} ∧
          (∀ c : ℝ, c < t * (2 / 3) ∨ t < c → (H '' d) ∩ {x | A x = c} = ∅) ∧
          (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
            IsFinitePLBallPair (ℝ × ℝ) ((H '' d) ∩ {x | A x ≤ t * a})
              ((H '' d) ∩ {x | A x = t * a})) ∧
          (∀ c ∈ Ioo (0 : ℝ) t, c ≠ t * (2 / 3) →
            HasDisjointPolygonPresentation ((H '' (s ∪ d)) ∩ {x | A x = c})) ∧
          ∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 → x ≠ H p →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) ∧
        (∃ u : ℝ, u ∈ Ioo 0 γ ∧ ∃ p : E, p ∈ d \ P.boundary ℝ ∧
          (G '' d) ∩ {x | (-A) x = u * (2 / 3)} = {G p} ∧
          (∀ c : ℝ, c < u * (2 / 3) ∨ u < c → (G '' d) ∩ {x | (-A) x = c} = ∅) ∧
          (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
            IsFinitePLBallPair (ℝ × ℝ) ((G '' d) ∩ {x | (-A) x ≤ u * a})
              ((G '' d) ∩ {x | (-A) x = u * a})) ∧
          (∀ c ∈ Ioo (0 : ℝ) u, c ≠ u * (2 / 3) →
            HasDisjointPolygonPresentation ((G '' (s' ∪ d)) ∩ {x | (-A) x = c})) ∧
          ∀ x ∈ G '' (s' ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 → x ≠ G p →
            x ∈ closure ((G '' (s' ∪ d)) ∩ {y | A y < A x}) ∧
              x ∈ closure ((G '' (s' ∪ d)) ∩ {y | A x < A y})) ∧
        ∀ c : ℝ, c ≠ 0 →
          (HasAlexanderCurvePresentation ((H '' (s ∪ d)) ∩ {x | A x = c}) 0 ∧
            HasAlexanderCurvePresentation ((G '' (s' ∪ d)) ∩ {x | A x = c}) 0) ∨
          ((∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
            ((H '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL) ∧
           (∃ F : (s' ∩ {x | A x = c} : Set E) ≃ₜ
            ((G '' (s' ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL)) := by
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
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, _, happroach,
      t, ht, p, hp, H, hglobalH, hPLH, hballH, hfixRH, hnegH, _, hfixH, hslabH,
      hraiseH, hzeroH, hsuccessorH, hminimumH, hemptyH, hdisksH,
      hcompareH, hlowH, _, hpositiveH, _⟩ :=
    M.exists_ordinary_intrinsic_deformation_with_band_geometry Mneg hregular
      (fun x hx hxA => hsource x hx
        ⟨(neg_lt_zero.mpr Mneg.width_pos).trans hxA.1, hxA.2⟩ hxA.1.ne')
      P hPe hPi hqP hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ
  have Mback : AlexanderCollarSlab S (-(-A)) q β := by simpa only [neg_neg] using M
  have hdplaneNeg : d ⊆ {x | (-A) x = 0} := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hdplane
  have hsectionNeg : S ∩ {x | (-A) x = 0} = P.boundary ℝ ∪ N.space := by
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hsection
  obtain ⟨r, _, hrlabels, _, _, _, _, hrside, _,
      u, hu, p', hp', G, hglobalG, hPLG, hballG, hfixRG, hnegG, _, hfixG, hslabG,
      hraiseG, hzeroG, hsuccessorG, hminimumG, hemptyG, hdisksG,
      hcompareG, hlowG, _, hpositiveG, _⟩ :=
    Mneg.exists_ordinary_intrinsic_deformation_with_band_geometry Mback hregularNeg
      (fun x hx hxA => hsourceNeg x hx
        ⟨(neg_lt_zero.mpr M.width_pos).trans hxA.1, hxA.2⟩ hxA.1.ne')
      P hPe hPi hqP hd hs₀ hs₁ hunion hinter hdplaneNeg hcap
      N hN hsectionNeg hdN hU hdU hδ
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
  have hcut : s ∩ s' ⊆ {x | A x = 0} :=
    hssinter.subset.trans (hd.1.trans hdplane)
  have hsignsH := H.mem_both_height_closures_of_raising_capped_image
    (F := {H p}) A A.continuous_of_finiteDimensional hs'.isCompact.isClosed
    hss hcut hdplane hraiseH (fun x hx hxA => hnegH x ⟨Or.inl hx, hxA⟩)
    hsource hpositiveH
  have hcutNeg : s' ∩ s ⊆ {x | (-A) x = 0} := by
    rw [inter_comm]
    simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hcut
  have hsignsGNeg := G.mem_both_height_closures_of_raising_capped_image
    (F := {G p'}) (-A) (-A).continuous_of_finiteDimensional hs.isCompact.isClosed
    ((union_comm s' s).trans hss) hcutNeg hdplaneNeg hraiseG
    (fun x hx hxA => hnegG x ⟨Or.inl hx, hxA⟩) hsourceNeg hpositiveG
  have hsignsG : ∀ x ∈ G '' (s' ∪ d), A x ∈ Ioo (-γ) β → A x ≠ 0 → x ≠ G p' →
      x ∈ closure ((G '' (s' ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((G '' (s' ∪ d)) ∩ {y | A x < A y}) := by
    intro x hx hxA hxzero hxne
    have hxA' : (-A) x ∈ Ioo (-β) γ := by
      change -β < -A x ∧ -A x < γ
      constructor <;> linarith [hxA.1, hxA.2]
    have hxzero' : (-A) x ≠ 0 := by
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_ne_zero] using hxzero
    obtain ⟨hlo, hhi⟩ := hsignsGNeg x hx hxA' hxzero' hxne
    exact ⟨by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_neg_iff] using hhi,
      by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_neg_iff] using hlo⟩
  have hlevel (c : ℝ) : {x : E | (-A) x = -c} = {x | A x = c} := by
    ext x
    change (-A x = -c) ↔ A x = c
    exact neg_inj
  have hcompareG' (c : ℝ) (hc : 0 < c ∨ c ≤ -u) :
      ∃ F : (s' ∩ {x | A x = c} : Set E) ≃ₜ
        ((G '' (s' ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL := by
    have hcNeg : -c < 0 ∨ u ≤ -c := by
      rcases hc with hc | hc
      · exact Or.inl (neg_lt_zero.mpr hc)
      · exact Or.inr (by linarith)
    obtain ⟨F, hF⟩ := hcompareG (-c) hcNeg
    have hsource := congrArg (s' ∩ ·) (hlevel c)
    have htarget := congrArg ((G '' (s' ∪ d)) ∩ ·) (hlevel c)
    exact ⟨(Homeomorph.setCongr hsource.symm).trans (F.trans (Homeomorph.setCongr htarget)),
      hF.setCongr hsource htarget⟩
  refine ⟨s, s', hlabels, hs, hs', hss, hssinter, H, G,
    hglobalH, hglobalG, hPLH, hPLG, hballH, hballG, hfixRH, hfixRG,
    (fun x hx => ⟨hfixH x hx, hfixG x hx⟩), ?_,
    (fun x hx hxA => hnegH x ⟨Or.inl hx, hxA⟩),
    (fun x hx hxA => hnegG x ⟨Or.inl hx, by
      change -A x < 0
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_zero] using hxA⟩),
    ?_, hzeroH, ?_, hsuccessorH, ?_,
    ⟨t, ht, p, hp, hminimumH, hemptyH, hdisksH, fun c hc => (hlowH c hc).2, hsignsH⟩,
    ⟨u, hu, p', hp', hminimumG, hemptyG, hdisksG, fun c hc => (hlowG c hc).2, hsignsG⟩,
    ?_⟩
  · intro x hx
    exact ⟨hslabH x hx, hslabG x
      (by simpa only [AffineMap.coe_neg, Pi.neg_apply, abs_neg] using hx)⟩
  · intro x
    exact ⟨hraiseH x, by
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_le_neg_iff] using hraiseG x⟩
  · simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hzeroG
  · intro hqs'
    have h := hsuccessorG hqs'
    exact ⟨by simpa only [neg_neg] using h.2, h.1⟩
  · apply ordinary_joint_level_alternatives A.continuous_of_finiteDimensional
      hs.isCompact.isClosed hs'.isCompact.isClosed hss hcut
      (fun c hc => hregular c ⟨hc.1, hc.2.trans ht.2⟩) (t := t) (u := u)
    · intro c hc
      have hreg := hregularNeg (-c)
        ⟨neg_pos.mpr hc.2, by linarith [hc.1, hu.2]⟩
      simpa only [hlevel c] using hreg
    · exact fun c hc => (hlowH c hc).1
    · intro c hc
      have hlow := (hlowG (-c)
        ⟨neg_pos.mpr hc.2, by linarith [hc.1]⟩).1
      simpa only [hlevel c] using hlow
    · exact hcompareH
    · exact hcompareG'

end Geometry
