import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSuccessor
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBaseRestriction
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveHeightCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveRemainderTransport










set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem AlexanderCollarSlab.exists_selected_successor_time_with_remainder
    {S s s' b d : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hinter : s ∩ s' ⊆ b) (hqs : q ∈ s)
    (hcap : d ∩ S = b) (hbd : b ⊆ d) (hd : d ⊆ {x | A x = 0})
    (N Ks Kd Kb : SimplicialComplex ℝ E)
    (hN : N.faces.Finite) (hKs : Ks.faces.Finite) (hKss : Ks.space = s)
    (hKd : Kd.faces.Finite) (hKds : Kd.space = d)
    (hKb : Kb.faces.Finite) (hKbs : Kb.space = b)
    (hB : S ∩ {x | A x = 0} = b ∪ N.space) (hdN : d ∩ N.space ⊆ {q})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    {g : E → ℝ} (hg : FinitePiecewiseAffineOn g M.collar)
    (hgN : ∀ x ∈ N.space, g x = 0) (hgq : g q = 0)
    (hgR : ∀ x ∈ M.residual, g x = 0)
    (v : E) (hv : A.linear v = 1) {ε : ℝ} (hε : 0 < ε)
    (H : Icc (-ε) ε → E ≃ₜ E)
    (hglobal : ∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
      FinitePiecewiseAffineOn (H t : E → E) L.space)
    (hformula : ∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v)
    (hall : ∀ t : Icc (-ε) ε, 0 < (t : ℝ) →
      (∀ x, A x ≤ A (H t x)) ∧
      (∀ x ∈ s, A x < 0 → H t x = x) ∧
      (∀ x, β ≤ A x → H t x = x) ∧
      ((H t '' (s ∪ d)) ∩ {x | A x = 0} = (N.space ∩ s) ∪ {q})) :
    ∃ t : Icc (-ε) ε, 0 < (t : ℝ) ∧
      Nonempty (AlexanderCollarSlab (H t '' (s ∪ d)) A q β) ∧
      ∃ TX TY : Set E, TX ⊆ M.collar ∧ TY ⊆ M.collar ∧ TX ⊆ s ∧ TY ⊆ s ∧
        M.collar ∩ s = TX ∪ TY ∧
        (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
            p.2 ∈ Icc 0 (M.upper p.1)},
          (M.chart p : E) ∈ TX ↔ (p : E × ℝ).1 ∈ (N.space ∩ s) ∪ {q}) ∧
        (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
            p.2 ∈ Icc 0 (M.upper p.1)},
          (M.chart p : E) ∈ TY ↔ (p : E × ℝ).1 ∈ b) ∧
        ∃ F : (TX ∪ (M.residual ∩ s) : Set E) ≃ₜ
            ((H t '' TX) ∪ (M.residual ∩ s) : Set E), F.IsFinitePL ∧
          (∀ x : (TX ∪ (M.residual ∩ s) : Set E), A (F x) = A x) ∧
          (∀ x : (M.residual ∩ s : Set E), (F ⟨x, Or.inr x.property⟩ : E) = x) ∧
          (∀ x : (TX ∪ (M.residual ∩ s) : Set E),
            (x : E) ∈ TX ↔ (F x : E) ∈ H t '' TX) ∧
          ∀ x : (TX ∪ (M.residual ∩ s) : Set E),
            (x : E) ∈ M.residual ∩ s ↔ (F x : E) ∈ M.residual ∩ s := by
  classical
  let X : Set E := (N.space ∩ s) ∪ {q}
  have hsS : s ⊆ S := subset_union_left.trans hunion.subset
  have hbB : b ⊆ S ∩ {x | A x = 0} := subset_union_left.trans hB.symm.subset
  have hkB : N.space ⊆ S ∩ {x | A x = 0} := subset_union_right.trans hB.symm.subset
  have hXB : X ⊆ S ∩ {x | A x = 0} := by
    rintro x (hx | hx)
    · exact hkB hx.1
    · exact (mem_singleton_iff.mp hx).symm ▸ And.intro M.apex_mem M.apex_height
  have hqX : q ∈ X := Or.inr rfl
  obtain ⟨J₀, hJ₀, hJ₀s⟩ := N.exists_finite_triangulation_inter Ks hN hKs
  rw [hKss] at hJ₀s
  obtain ⟨Jq, hJq, hJqs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion_convexHull
    (fun _ : Unit => ({q} : Finset E)) (fun _ => affineIndependent_of_subsingleton ℝ _)
  have hJqspace : Jq.space = {q} := by simpa using hJqs
  obtain ⟨KX, hKX, hKXs⟩ := J₀.exists_finite_triangulation_union Jq hJ₀ hJq
  rw [hJ₀s, hJqspace] at hKXs
  obtain ⟨TX, hTX, C, hC, hCval, hCX⟩ :=
    M.chart_finitePL.exists_collar_base_restriction M.width_pos
      (fun x hx => (M.upper_bounds x hx).2) hXB KX hKX hKXs
  obtain ⟨TY, hTY, CY, hCY, _, hCYb⟩ :=
    M.chart_finitePL.exists_collar_base_restriction M.width_pos
      (fun x hx => (M.upper_bounds x hx).2) hbB Kb hKb hKbs
  have hcopy := hCY.symm
  obtain ⟨_, ⟨KY, hKY, hKYs, _⟩, _⟩ := hcopy
  have htouch : b ∩ N.space ⊆ {q} := fun _ hx => hdN ⟨hbd hx.1, hx.2⟩
  obtain ⟨hXs, hYs, hsplit, _, _, hcontact⟩ := M.selected_collar_decomposition
    hs hs' hunion hinter hB htouch hqs hcap hselected hTX hTY hCX hCYb
  have hTYzero : TY ∩ {x | A x = 0} ⊆ d :=
    (M.restricted_collar_zero_subset hTY (fun p hp => (hCYb p).mp hp)).trans hbd
  have hCheight : ∀ p, A (C p) = (p : E × ℝ).2 := by
    intro p
    rw [hCval]
    exact M.height _
  have hCcontact : ∀ p, (C p : E) ∈ M.residual ↔
      (p : E × ℝ).2 = M.upper (p : E × ℝ).1 := by
    intro p
    rw [hCval]
    exact M.roof_contact _
  have hCcopy := hC.symm
  obtain ⟨_, ⟨KT, hKT, hKTs, _⟩, _⟩ := hCcopy
  have hgT : FinitePiecewiseAffineOn g TX :=
    hKTs ▸ hg.restrict KT hKT (hKTs.subset.trans hTX)
  have hgbottom (p : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (M.upper p.1)})
      (hp : (p : E × ℝ).2 = 0) : g (C p) = 0 := by
    rw [hCval, M.bottom _ hp]
    rcases p.property.1 with hx | hx
    · exact hgN _ hx.1
    · exact (mem_singleton_iff.mp hx).symm ▸ hgq
  obtain ⟨δ, hδ, hcoords⟩ := hC.exists_moved_collar_height_coordinates_with_endpoints
    (fun x hx => (M.upper_bounds x (hXB hx)).1) A hCheight hCcontact hgT
    hgbottom (fun p hp => hgR _ ((hCcontact p).mpr hp)) v hv
  let r := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have hrδ : r < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)
  let t : Icc (-ε) ε := ⟨r, by constructor <;> linarith⟩
  have ht : 0 < (t : ℝ) := hr
  have habs : |(t : ℝ)| < δ := by rw [abs_of_pos ht]; exact hrδ
  have hHt : FinitePiecewiseAffineOn (H t : E → E) TX := hKTs ▸ hglobal t KT hKT
  obtain ⟨D, hD, hDheight, hDfix, hDcontact⟩ := hcoords t habs (H t) hHt
    (fun x _ => hformula t x)
  obtain ⟨hraise, hneg, hhigh, hzeroX⟩ := hall t ht
  have hfixR (x : E) (hx : x ∈ M.residual) : H t x = x := by
    rw [hformula, hgR x hx, mul_zero, zero_smul, add_zero]
  have hcapzero : (H t '' d) ∩ {x | A x = 0} ⊆ {q} := by
    rintro y ⟨⟨x, hx, hxy⟩, hyzero⟩
    have hyX : y ∈ X := hzeroX.subset ⟨⟨x, Or.inr hx, hxy⟩, hyzero⟩
    have hgy : g y = 0 := by
      rcases hyX with hy | hy
      · exact hgN y hy.1
      · exact (mem_singleton_iff.mp hy).symm ▸ hgq
    have hfixy : H t y = y := by rw [hformula, hgy, mul_zero, zero_smul, add_zero]
    have hxy' : x = y := (H t).injective (hxy.trans hfixy.symm)
    rcases hyX with hy | hy
    · exact hdN ⟨hxy' ▸ hx, hy.1⟩
    · exact hy
  have hsuccessor := M.nonempty_selected_successor hsS hsplit hd hcontact hTYzero
    (H t) hraise hneg hhigh hfixR hcapzero (hglobal t) hzeroX hXB hqX
    Ks Kd KY KX hKs hKss hKd hKds hKY hKYs hKX hKXs D hD hDheight
    (fun p hp => (hDfix p (Or.inl hp)).trans ((hCval p).trans (M.bottom _ hp))) hDcontact
  have himageR : H t '' M.residual = M.residual := by
    apply Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      rwa [hfixR y hy]
    · exact fun x hx => ⟨x, hx, hfixR x hx⟩
  have hRcontact₀ : ∀ p : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (M.upper p.1)},
      (C p : E) ∈ M.residual ∩ s ↔ (p : E × ℝ).2 = M.upper (p : E × ℝ).1 := by
    intro p
    exact ⟨fun hp => (hCcontact p).mp hp.1,
      fun hp => ⟨(hCcontact p).mpr hp, hXs (C p).property⟩⟩
  have hRcontact₁ : ∀ p : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (M.upper p.1)},
      (D p : E) ∈ M.residual ∩ s ↔ (p : E × ℝ).2 = M.upper (p : E × ℝ).1 := by
    intro p
    constructor
    · exact fun hp => (hDcontact p).mp (himageR.symm.subset hp.1)
    · intro hp
      rw [hDfix p (Or.inr hp)]
      exact (hRcontact₀ p).mpr hp
  obtain ⟨JR, hJR, hJRs⟩ := M.residualComplex.exists_finite_triangulation_inter Ks
    M.residual_finite hKs
  rw [M.residual_space, hKss] at hJRs
  obtain ⟨F, hF, hFA, hFR, _, hFT, hFRmem⟩ :=
    hC.exists_height_preserving_union_fixing_residual
      (q := {p : E × ℝ | p.2 = M.upper p.1}) hD hRcontact₀ hRcontact₁
      (fun p hp => (hDfix p (Or.inr hp)).symm) JR hJR hJRs A
      (fun p => (hDheight p).trans (hCheight p).symm)
  exact ⟨t, ht, hsuccessor, TX, TY, hTX, hTY, hXs, hYs, hsplit,
    hCX, hCYb, F, hF, hFA, hFR, hFT, hFRmem⟩




theorem AlexanderCollarSlab.exists_selected_successor_time
    {S s s' b d : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hinter : s ∩ s' ⊆ b) (hqs : q ∈ s)
    (hcap : d ∩ S = b) (hbd : b ⊆ d) (hd : d ⊆ {x | A x = 0})
    (N Ks Kd Kb : SimplicialComplex ℝ E)
    (hN : N.faces.Finite) (hKs : Ks.faces.Finite) (hKss : Ks.space = s)
    (hKd : Kd.faces.Finite) (hKds : Kd.space = d)
    (hKb : Kb.faces.Finite) (hKbs : Kb.space = b)
    (hB : S ∩ {x | A x = 0} = b ∪ N.space) (hdN : d ∩ N.space ⊆ {q})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    {g : E → ℝ} (hg : FinitePiecewiseAffineOn g M.collar)
    (hgN : ∀ x ∈ N.space, g x = 0) (hgq : g q = 0)
    (hgR : ∀ x ∈ M.residual, g x = 0)
    (v : E) (hv : A.linear v = 1) {ε : ℝ} (hε : 0 < ε)
    (H : Icc (-ε) ε → E ≃ₜ E)
    (hglobal : ∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
      FinitePiecewiseAffineOn (H t : E → E) L.space)
    (hformula : ∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v)
    (hall : ∀ t : Icc (-ε) ε, 0 < (t : ℝ) →
      (∀ x, A x ≤ A (H t x)) ∧
      (∀ x ∈ s, A x < 0 → H t x = x) ∧
      (∀ x, β ≤ A x → H t x = x) ∧
      ((H t '' (s ∪ d)) ∩ {x | A x = 0} = (N.space ∩ s) ∪ {q})) :
    ∃ t : Icc (-ε) ε, 0 < (t : ℝ) ∧
      Nonempty (AlexanderCollarSlab (H t '' (s ∪ d)) A q β) := by
  obtain ⟨t, ht, hsuccessor, _⟩ := M.exists_selected_successor_time_with_remainder
    hs hs' hunion hinter hqs hcap hbd hd N Ks Kd Kb hN hKs hKss hKd hKds hKb hKbs
    hB hdN hselected hg hgN hgq hgR v hv hε H hglobal hformula hall
  exact ⟨t, ht, hsuccessor⟩

end Geometry
