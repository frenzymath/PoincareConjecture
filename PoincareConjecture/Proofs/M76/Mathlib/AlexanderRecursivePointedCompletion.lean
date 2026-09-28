import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCutSide
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursivePointedFamily
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursivePointedSuccessor
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursivePointedSigns

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AlexanderCollarSlab.exists_pointed_capped_deformation_with_successor_and_signs {S : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β)
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
        ((∀ x ∈ S, A x ∈ Ioo (0 : ℝ) β →
            x ∈ closure (S ∩ {y | A y < A x}) ∧
              x ∈ closure (S ∩ {y | A x < A y})) →
          ∀ x ∈ H '' (s ∪ d), A x ∈ Ioo (0 : ℝ) β →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) ∧
        ∀ c : ℝ, c ≠ 0 →
          ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
              ((H '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL ∧
            ∀ x : ((M.residual ∩ s) ∩ {x | A x = c} : Set E),
              ∃ y : (s ∩ {x | A x = c} : Set E), (y : E) = x ∧ (F y : E) = x := by
  have hP : P.boundary ℝ ⊆ S ∩ {x | A x = 0} :=
    subset_union_left.trans hsection.symm.subset
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, hselected, hside, happroach⟩ :=
    M.exists_selected_cut_side P hPe hPi hd hs₀ hs₁ hunion hinter hdplane hcap
      N hN hsection hdN
  obtain ⟨ec⟩ := P.nonempty_boundary_homeomorph_circle hPe hPi
  have hbconn := isConnected_sdiff_singleton_of_homeomorph_circle (P.boundary ℝ) ec q
  obtain ⟨x, hx⟩ := hbconn.nonempty
  obtain ⟨v, hv⟩ := M.exists_unit_height_direction (hP hx.1) hx.2
  let V : Set E := U ∩ {x | |A x| < δ}
  have hV : IsOpen V := hU.inter
    (isOpen_lt A.continuous_of_finiteDimensional.abs continuous_const)
  have hdV : d ⊆ V := fun x hx => ⟨hdU hx, by
    change |A x| < δ
    rw [hdplane hx, abs_zero]
    exact hδ⟩
  obtain ⟨g, hg, hgrange, hgmax, hgsigns, hgN, hgq, hgR,
      ε₀, hε₀, H₀, hglobal₀, _, _, hformula₀, hall₀⟩ :=
    M.exists_pointed_capped_family_with_signs hs hs'.isCompact.isClosed hd hdplane hqP hss
      hssinter.subset hcap hbconn N hN hsection hdN hside hselected v hv hV hdV
  have hscopy := hs
  have hdcopy := hd
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Ks, hKs, hKss, _⟩, _⟩, _⟩ := hscopy
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Kd, hKd, hKds, _⟩, _⟩, _⟩ := hdcopy
  obtain ⟨κ, hκ, hsigns⟩ := M.exists_pointed_sign_interval hs.isCompact.isClosed
    hs'.isCompact.isClosed hss hssinter.subset hs.1 hd.1 hdplane hsection
    hselected Ks hKs hKss hg hgN hgq hgR hgrange hgmax
    (fun x hx => (hgsigns x hx).1) (fun x hx => (hgsigns x hx).2) v hv
  let ε := min ε₀ (κ / 2)
  have hε : 0 < ε := lt_min hε₀ (half_pos hκ)
  have hεle : ε ≤ ε₀ := min_le_left _ _
  have hεκ : ε < κ := (min_le_right _ _).trans_lt (half_lt_self hκ)
  let embed : Icc (-ε) ε → Icc (-ε₀) ε₀ := fun t =>
    ⟨t, (neg_le_neg hεle).trans t.property.1, t.property.2.trans hεle⟩
  let H : Icc (-ε) ε → E ≃ₜ E := fun t => H₀ (embed t)
  have hglobal (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) :
      FinitePiecewiseAffineOn (H t : E → E) L.space := hglobal₀ (embed t) L hL
  have hformula (t : Icc (-ε) ε) (x : E) : H t x = x + ((t : ℝ) * g x) • v :=
    hformula₀ (embed t) x
  obtain ⟨t, ht, hsuccessor⟩ := M.exists_pointed_successor_time hs.isCompact.isClosed
    hs'.isCompact.isClosed hss hssinter.subset (hs.1 hqP) hqP hcap hd.1 hdplane
    N Ks Kd (P.simplicialComplex hPe) hN hKs hKss hKd hKds
    (P.finite_simplicialComplex_faces hPe) (P.simplicialComplex_space hPe)
    hsection hdN hselected hg hgN hgq hgR v hv hε H hglobal hformula
    (fun t ht => by
      obtain ⟨_, _, _, hneg, _, hhigh, hpositive⟩ := hall₀ (embed t)
      obtain ⟨hraise, hzero, _⟩ := hpositive ht
      exact ⟨hraise, fun x hx hxA => hneg x ⟨Or.inl hx, hxA⟩, hhigh, hzero⟩)
  obtain ⟨hPL, hball, hfixR, hneg, hfixV, hhigh, hpositive⟩ := hall₀ (embed t)
  obtain ⟨hraise, hzero, hlevels⟩ := hpositive ht
  have htκ : |(t : ℝ)| < κ := (abs_le.mpr t.property).trans_lt hεκ
  have hchild := hsigns t ht htκ (H t) (hglobal t) (hformula t)
    (fun x _ => hraise x) (fun x hx hxA => hneg x ⟨Or.inl hx, hxA⟩)
  refine ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
    H t, hglobal t, hPL, hball, hfixR, hneg, ?_, ?_, hhigh, hraise,
    hzero, hsuccessor, hchild, hlevels⟩
  · exact fun x hx => hfixV x (fun h => hx h.1)
  · exact fun x hx => hfixV x (fun h => (not_lt_of_ge hx) h.2)

theorem AlexanderCollarSlab.exists_pointed_capped_deformation_with_successor {S : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β)
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
        ∀ c : ℝ, c ≠ 0 →
          ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
              ((H '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL ∧
            ∀ x : ((M.residual ∩ s) ∩ {x | A x = c} : Set E),
              ∃ y : (s ∩ {x | A x = c} : Set E), (y : E) = x ∧ (F y : E) = x := by
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
      H, hglobal, hPL, hball, hfixR, hneg, hfixU, hfixδ, hhigh, hraise,
      hzero, hsuccessor, _, hlevels⟩ :=
    M.exists_pointed_capped_deformation_with_successor_and_signs P hPe hPi hqP
      hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ
  exact ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
    H, hglobal, hPL, hball, hfixR, hneg, hfixU, hfixδ, hhigh, hraise,
    hzero, hsuccessor, hlevels⟩

end Geometry
