import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicOrdinaryFamily
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveOrdinarySuccessor
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveOrdinaryNegative
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveOrdinaryRemainder
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedHeight
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCapSigns
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveOrdinaryTerminal
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveRimLevel











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]








theorem AlexanderCollarSlab.exists_ordinary_capped_deformation_with_band_geometry
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab S A q β) (Mneg : AlexanderCollarSlab S (-A) q γ)
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
            ∃ (Z : Set E) (f : E → E) (X Y : Set E),
              FinitePiecewiseAffineOn f Z ∧ InjOn f Z ∧ P.boundary ℝ ⊆ Z ∧
              s ∩ {x | A x = c} = (f '' P.boundary ℝ) ∪ X ∧
              Disjoint (f '' P.boundary ℝ) X ∧
              (H '' (s ∪ d)) ∩ {x | A x = c} = ((H '' d) ∩ {x | A x = c}) ∪ Y ∧
              Disjoint ((H '' d) ∩ {x | A x = c}) Y ∧
              ∃ F : X ≃ₜ Y, F.IsFinitePL) ∧
          (∀ a b : ℝ, t < a → b ≤ β →
            ∃ G : (s ∩ {x | A x ∈ Icc a b} : Set E) ≃ₜ
                ((H '' (s ∪ d)) ∩ {x | A x ∈ Icc a b} : Set E),
              G.IsFinitePL ∧ ∀ x, A (G x) = A x) ∧
          (∀ x ∈ H '' d, x ≠ H p →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) ∧
          ∃ TX TY : Set E, TX ⊆ M.collar ∧ TY ⊆ M.collar ∧ TX ⊆ s ∧ TY ⊆ s ∧
            M.collar ∩ s = TX ∪ TY ∧ Disjoint TX TY ∧ Disjoint d TX ∧
            (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
                p.2 ∈ Icc 0 (M.upper p.1)},
              (M.chart p : E) ∈ TX ↔ (p : E × ℝ).1 ∈ N.space ∩ s) ∧
            (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
                p.2 ∈ Icc 0 (M.upper p.1)},
              (M.chart p : E) ∈ TY ↔ (p : E × ℝ).1 ∈ P.boundary ℝ) ∧
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
  classical
  have hP : P.boundary ℝ ⊆ S ∩ {x | A x = 0} :=
    subset_union_left.trans hsection.symm.subset
  have hqd : q ∉ d := fun h => hqP (hcap.subset ⟨h, M.apex_mem⟩)
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
  obtain ⟨g, hg, hgN, hgR, hgb, p, hp, ε, hε, hεroof, H, hglobal, _, _, hformula,
      hall⟩ := M.exists_ordinary_capped_family_with_rim_scalar
    P hPe hPi hqd hd hs hs'.isCompact.isClosed
      hss hssinter.subset hdplane hcap N hN hsection hdN hselected v hv hV hdV
  have hscopy := hs
  have hdcopy := hd
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Ks, hKs, hKss, _⟩, _⟩, _⟩ := hscopy
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Kd, hKd, hKds, _⟩, _⟩, _⟩ := hdcopy
  have hbN : Disjoint (P.boundary ℝ) N.space := by
    apply disjoint_left.mpr
    intro x hx hy
    have hxq : x = q := hdN ⟨hd.1 hx, hy⟩
    exact hqd (hxq ▸ hd.1 hx)
  obtain ⟨TX, TY, hTX, hTY, hXs, hYs, hsplit, hdisj, hdcap, hCX, hCY,
      η, hη, hrem⟩ := M.exists_ordinary_remainder_interval hs.isCompact.isClosed
    hs'.isCompact.isClosed hss hssinter.subset hcap N Ks (P.simplicialComplex hPe)
    hN hKs hKss (P.finite_simplicialComplex_faces hPe) (P.simplicialComplex_space hPe)
    hsection hbN hselected hg hgN hgR v hv
  obtain ⟨κ₀, hκ₀, hselectedHeights⟩ :=
    M.exists_selected_fiber_strict_height_bound hg hgb v hv
  have hgbound (x : E) (hx : x ∈ s ∩ {x | A x = 0}) : g x ≤ 1 := by
    rcases hsection.subset ⟨hss.subset (Or.inl hx.1), hx.2⟩ with hxr | hxN
    · rw [hgb x hxr]
    · rw [hgN x hxN]
      exact zero_le_one
  obtain ⟨κ₁, hκ₁, hterminal⟩ := M.exists_ordinary_terminal_interval
    hs.isCompact.isClosed hs'.isCompact.isClosed hss hssinter.subset hs.1
      (fun x hx => (hP hx).2) hselected Ks hKs hKss hg hgbound hgR v hv
  let κ := min κ₀ κ₁
  have hκ : 0 < κ := lt_min hκ₀ hκ₁
  let ρ := min ε (min η κ) / 2
  have hsmall : 0 < min ε (min η κ) := lt_min hε.1 (lt_min hη hκ)
  have hρ : 0 < ρ := half_pos hsmall
  have hρε : ρ < ε := (half_lt_self hsmall).trans_le (min_le_left _ _)
  have hρη : ρ < η :=
    (half_lt_self hsmall).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hρκ : ρ < κ :=
    (half_lt_self hsmall).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let embed : Icc (-ρ) ρ → Icc (-ε) ε := fun t =>
    ⟨t, (neg_le_neg hρε.le).trans t.property.1, t.property.2.trans hρε.le⟩
  have htime : ∃ t : Icc (-ε) ε, 0 < (t : ℝ) ∧ |(t : ℝ)| < η ∧ |(t : ℝ)| < κ ∧
      (q ∈ s → Nonempty (AlexanderCollarSlab (H t '' (s ∪ d)) A q β)) := by
    by_cases hqs : q ∈ s
    · obtain ⟨t, ht, hsuccessor⟩ := M.exists_ordinary_successor_time
        hs.isCompact.isClosed hs'.isCompact.isClosed hss hssinter.subset hqs hqd
        hcap hd.1 hdplane N Ks Kd (P.simplicialComplex hPe) hN hKs hKss hKd hKds
        (P.finite_simplicialComplex_faces hPe) (P.simplicialComplex_space hPe)
        hsection hdN hselected hg hgN hgR v hv hρ (fun t => H (embed t))
        (fun t L hL => hglobal (embed t) L hL) (fun t x => hformula (embed t) x)
        (fun t ht => by
          obtain ⟨_, hneg, _, hhigh, _, hpositive⟩ := hall (embed t)
          obtain ⟨hraise, hzero, _⟩ := hpositive ht
          exact ⟨hraise, fun x hx hxA => hneg x ⟨Or.inl hx, hxA⟩, hhigh, hzero⟩)
      refine ⟨embed t, ht, ?_, ?_, fun _ => hsuccessor⟩
      · change |(t : ℝ)| < η
        rw [abs_of_pos ht]
        exact t.property.2.trans_lt hρη
      · change |(t : ℝ)| < κ
        rw [abs_of_pos ht]
        exact t.property.2.trans_lt hρκ
    · let t : Icc (-ε) ε := ⟨ρ, (neg_lt_zero.mpr hε.1).le.trans hρ.le, hρε.le⟩
      exact ⟨t, hρ, by change |ρ| < η; rw [abs_of_pos hρ]; exact hρη,
        by change |ρ| < κ; rw [abs_of_pos hρ]; exact hρκ,
        fun h => (hqs h).elim⟩
  obtain ⟨t, ht, htη, htκ, hsuccessor⟩ := htime
  have htκ₀ : |(t : ℝ)| < κ₀ := htκ.trans_le (min_le_left _ _)
  obtain ⟨F, hF, hFA, hFR, hFT, hFRmem⟩ := hrem t htη (H t) (hglobal t) (hformula t)
  have hselectedHeight (x : E) (hx : x ∈ TY) : (t : ℝ) ≤ A (H t x) := by
    let p := M.chart.symm ⟨x, hTY hx⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    have h := (hselectedHeights t htκ₀ (H t : E → E) (fun x _ => hformula t x) p
      ((hCY p).mp (hp.symm ▸ hx))).1
    rwa [hp] at h
  have hselectedRim (x : E) (hx : x ∈ TY) (hAx : A (H t x) = (t : ℝ)) :
      x ∈ P.boundary ℝ :=
    M.mem_rim_of_selected_image_height_eq hTY (fun w hw => (hCY w).mp hw)
      (H t) (fun w hw hpos => (hselectedHeights t htκ₀ (H t : E → E)
        (fun x _ => hformula t x) w hw).2 hpos) hx hAx
  obtain ⟨hfixR, hneg, hfixV, hhigh, hball, hpositive⟩ := hall t
  obtain ⟨hraise, hzero, hminimum, hempty, hdisks, hlevels, hlow⟩ := hpositive ht
  have hcapBound (x : E) (hx : x ∈ d) : A (H t x) ≤ (t : ℝ) := by
    apply le_of_not_gt
    intro hgt
    have hmem : H t x ∈ (H t '' d) ∩ {y | A y = A (H t x)} :=
      ⟨mem_image_of_mem (H t) hx, rfl⟩
    rw [hempty _ (Or.inr hgt)] at hmem
    exact hmem
  have hterminalBands := hterminal t ht (htκ.trans_le (min_le_right _ _))
    (H t) (hglobal t) (hformula t) (fun x _ => hraise x)
      (fun x hx hxA => hneg x ⟨Or.inl hx, hxA⟩) d hcapBound
  have hcapSigns (x : E) (hx : x ∈ H t '' d) (hne : x ≠ H t p) :
      x ∈ closure ((H t '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H t '' (s ∪ d)) ∩ {y | A x < A y}) := by
    apply M.ordinary_cap_mem_both_height_closures hP hqP (H t) ht hselected
      (fun w hw => (hselectedHeights t htκ₀ (H t : E → E)
        (fun x _ => hformula t x) w hw).2) hball hempty hdisks x hx
    intro heq
    have hbirth : x ∈ (H t '' d) ∩ {y | A y = (t : ℝ) * (2 / 3)} := ⟨hx, heq⟩
    rw [hminimum] at hbirth
    exact hne hbirth
  have hnegative (hqs : q ∈ s) :=
    Mneg.nonempty_ordinary_fixed_negative_successor P hPe hPi hd hs hs'
      hss hssinter hqs hqd hdplane N hN hsection hdN hside (H t) hraise hneg hzero
  obtain ⟨J, hJ, hJs⟩ := Ks.exists_finite_triangulation_union Kd hKs hKd
  rw [hKss, hKds] at hJs
  have hPL : FinitePiecewiseAffineOn (H t : E → E) (s ∪ d) :=
    hJs ▸ hglobal t J hJ
  refine ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
    t, ⟨ht, t.property.2.trans_lt hε.2⟩, p, hp, H t,
    hglobal t, hPL, hball, hfixR, hneg, hhigh, ?_, ?_, hraise, hzero,
    (fun hqs => ⟨hsuccessor hqs, hnegative hqs⟩),
    hminimum, hempty, hdisks, hlevels, hlow, hterminalBands, hcapSigns,
    TX, TY, hTX, hTY, hXs, hYs, hsplit,
    hdisj, hdcap, hCX, hCY, F, hF, hFA, hFR, hFT, hFRmem,
    (fun x hx => t.property.2.trans_lt (hεroof x hx)), hselectedHeight, hselectedRim⟩
  · exact fun x hx => hfixV x (fun h => hx h.1)
  · exact fun x hx => hfixV x (fun h => (not_lt_of_ge hx) h.2)




theorem AlexanderCollarSlab.exists_ordinary_capped_deformation_with_remainder_and_cap_signs
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab S A q β) (Mneg : AlexanderCollarSlab S (-A) q γ)
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
            ∃ (Z : Set E) (f : E → E) (X Y : Set E),
              FinitePiecewiseAffineOn f Z ∧ InjOn f Z ∧ P.boundary ℝ ⊆ Z ∧
              s ∩ {x | A x = c} = (f '' P.boundary ℝ) ∪ X ∧
              Disjoint (f '' P.boundary ℝ) X ∧
              (H '' (s ∪ d)) ∩ {x | A x = c} = ((H '' d) ∩ {x | A x = c}) ∪ Y ∧
              Disjoint ((H '' d) ∩ {x | A x = c}) Y ∧
              ∃ F : X ≃ₜ Y, F.IsFinitePL) ∧
          (∀ x ∈ H '' d, x ≠ H p →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) ∧
          ∃ TX TY : Set E, TX ⊆ M.collar ∧ TY ⊆ M.collar ∧ TX ⊆ s ∧ TY ⊆ s ∧
            M.collar ∩ s = TX ∪ TY ∧ Disjoint TX TY ∧ Disjoint d TX ∧
            (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
                p.2 ∈ Icc 0 (M.upper p.1)},
              (M.chart p : E) ∈ TX ↔ (p : E × ℝ).1 ∈ N.space ∩ s) ∧
            (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
                p.2 ∈ Icc 0 (M.upper p.1)},
              (M.chart p : E) ∈ TY ↔ (p : E × ℝ).1 ∈ P.boundary ℝ) ∧
            ∃ F : (TX ∪ (M.residual ∩ s) : Set E) ≃ₜ
                ((H '' TX) ∪ (M.residual ∩ s) : Set E), F.IsFinitePL ∧
              (∀ x : (TX ∪ (M.residual ∩ s) : Set E), A (F x) = A x) ∧
              (∀ x : (M.residual ∩ s : Set E), (F ⟨x, Or.inr x.property⟩ : E) = x) ∧
              (∀ x : (TX ∪ (M.residual ∩ s) : Set E),
                (x : E) ∈ TX ↔ (F x : E) ∈ H '' TX) ∧
              (∀ x : (TX ∪ (M.residual ∩ s) : Set E),
                (x : E) ∈ M.residual ∩ s ↔ (F x : E) ∈ M.residual ∩ s) ∧
              (∀ x ∈ P.boundary ℝ, t < M.upper x) ∧
              ∀ x ∈ TY, t ≤ A (H x) := by
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
      t, ht, p, hp, H, hglobal, hPL, hball, hfixR, hneg, hhigh, hfix, hslab,
      hraise, hzero, hsuccessor, hminimum, hempty, hdisks, hlevels, hlow,
      _, hcapSigns, hrem⟩ :=
    M.exists_ordinary_capped_deformation_with_band_geometry
      Mneg P hPe hPi hqP hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ
  obtain ⟨TX, TY, hTX, hTY, hXs, hYs, hsplit, hdisj, hdcap, hCX, hCY,
      F, hF, hFA, hFR, hFT, hFRmem, hroof, hmoved, _⟩ := hrem
  exact ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
    t, ht, p, hp, H, hglobal, hPL, hball, hfixR, hneg, hhigh, hfix, hslab,
    hraise, hzero, hsuccessor, hminimum, hempty, hdisks, hlevels, hlow, hcapSigns,
    TX, TY, hTX, hTY, hXs, hYs, hsplit, hdisj, hdcap, hCX, hCY,
    F, hF, hFA, hFR, hFT, hFRmem, hroof, hmoved⟩





theorem AlexanderCollarSlab.exists_ordinary_capped_deformation_with_remainder
    {S : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab S A q β) (Mneg : AlexanderCollarSlab S (-A) q γ)
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
            ∃ (Z : Set E) (f : E → E) (X Y : Set E),
              FinitePiecewiseAffineOn f Z ∧ InjOn f Z ∧ P.boundary ℝ ⊆ Z ∧
              s ∩ {x | A x = c} = (f '' P.boundary ℝ) ∪ X ∧
              Disjoint (f '' P.boundary ℝ) X ∧
              (H '' (s ∪ d)) ∩ {x | A x = c} = ((H '' d) ∩ {x | A x = c}) ∪ Y ∧
              Disjoint ((H '' d) ∩ {x | A x = c}) Y ∧
              ∃ F : X ≃ₜ Y, F.IsFinitePL) ∧
          ∃ TX TY : Set E, TX ⊆ M.collar ∧ TY ⊆ M.collar ∧ TX ⊆ s ∧ TY ⊆ s ∧
            M.collar ∩ s = TX ∪ TY ∧ Disjoint TX TY ∧ Disjoint d TX ∧
            (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
                p.2 ∈ Icc 0 (M.upper p.1)},
              (M.chart p : E) ∈ TX ↔ (p : E × ℝ).1 ∈ N.space ∩ s) ∧
            (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
                p.2 ∈ Icc 0 (M.upper p.1)},
              (M.chart p : E) ∈ TY ↔ (p : E × ℝ).1 ∈ P.boundary ℝ) ∧
            ∃ F : (TX ∪ (M.residual ∩ s) : Set E) ≃ₜ
                ((H '' TX) ∪ (M.residual ∩ s) : Set E), F.IsFinitePL ∧
              (∀ x : (TX ∪ (M.residual ∩ s) : Set E), A (F x) = A x) ∧
              (∀ x : (M.residual ∩ s : Set E), (F ⟨x, Or.inr x.property⟩ : E) = x) ∧
              (∀ x : (TX ∪ (M.residual ∩ s) : Set E),
                (x : E) ∈ TX ↔ (F x : E) ∈ H '' TX) ∧
              (∀ x : (TX ∪ (M.residual ∩ s) : Set E),
                (x : E) ∈ M.residual ∩ s ↔ (F x : E) ∈ M.residual ∩ s) ∧
              (∀ x ∈ P.boundary ℝ, t < M.upper x) ∧
              ∀ x ∈ TY, t ≤ A (H x) := by
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
      t, ht, p, hp, H, hglobal, hPL, hball, hfixR, hneg, hhigh, hfix, hslab,
      hraise, hzero, hsuccessor, hminimum, hempty, hdisks, hlevels, hlow, _, hrem⟩ :=
    M.exists_ordinary_capped_deformation_with_remainder_and_cap_signs
      Mneg P hPe hPi hqP hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ
  exact ⟨s, s', hlabels, hs, hs', hss, hssinter, hside, happroach,
    t, ht, p, hp, H, hglobal, hPL, hball, hfixR, hneg, hhigh, hfix, hslab,
    hraise, hzero, hsuccessor, hminimum, hempty, hdisks, hlevels, hlow, hrem⟩

end Geometry
