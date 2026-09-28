import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveOrdinaryPieces
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBaseRestriction
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveHeightCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveRemainderTransport
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem AlexanderCollarSlab.exists_ordinary_remainder_interval
    {S s s' b d : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hinter : s ∩ s' ⊆ b) (hcap : d ∩ S = b)
    (N Ks Kb : SimplicialComplex ℝ E)
    (hN : N.faces.Finite) (hKs : Ks.faces.Finite) (hKss : Ks.space = s)
    (hKb : Kb.faces.Finite) (hKbs : Kb.space = b)
    (hB : S ∩ {x | A x = 0} = b ∪ N.space) (htouch : Disjoint b N.space)
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    {g : E → ℝ} (hg : FinitePiecewiseAffineOn g M.collar)
    (hgN : ∀ x ∈ N.space, g x = 0) (hgR : ∀ x ∈ M.residual, g x = 0)
    (v : E) (hv : A.linear v = 1) :
    ∃ TX TY : Set E, TX ⊆ M.collar ∧ TY ⊆ M.collar ∧ TX ⊆ s ∧ TY ⊆ s ∧
      M.collar ∩ s = TX ∪ TY ∧ Disjoint TX TY ∧ Disjoint d TX ∧
      (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (M.upper p.1)},
        (M.chart p : E) ∈ TX ↔ (p : E × ℝ).1 ∈ N.space ∩ s) ∧
      (∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (M.upper p.1)},
        (M.chart p : E) ∈ TY ↔ (p : E × ℝ).1 ∈ b) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ H : E ≃ₜ E,
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H : E → E) L.space) →
        (∀ x : E, H x = x + (t * g x) • v) →
        ∃ F : (TX ∪ (M.residual ∩ s) : Set E) ≃ₜ
            ((H '' TX) ∪ (M.residual ∩ s) : Set E), F.IsFinitePL ∧
          (∀ x : (TX ∪ (M.residual ∩ s) : Set E), A (F x) = A x) ∧
          (∀ x : (M.residual ∩ s : Set E), (F ⟨x, Or.inr x.property⟩ : E) = x) ∧
          (∀ x : (TX ∪ (M.residual ∩ s) : Set E),
            (x : E) ∈ TX ↔ (F x : E) ∈ H '' TX) ∧
          ∀ x : (TX ∪ (M.residual ∩ s) : Set E),
            (x : E) ∈ M.residual ∩ s ↔ (F x : E) ∈ M.residual ∩ s := by
  classical
  let X := N.space ∩ s
  have hXB : X ⊆ S ∩ {x | A x = 0} :=
    inter_subset_left.trans (subset_union_right.trans hB.symm.subset)
  have hbB : b ⊆ S ∩ {x | A x = 0} := subset_union_left.trans hB.symm.subset
  obtain ⟨KX, hKX, hKXs⟩ := N.exists_finite_triangulation_inter Ks hN hKs
  rw [hKss] at hKXs
  obtain ⟨TX, hTX, C, hC, hCval, hCX⟩ :=
    M.chart_finitePL.exists_collar_base_restriction M.width_pos
      (fun x hx => (M.upper_bounds x hx).2) hXB KX hKX hKXs
  obtain ⟨TY, hTY, _, _, _, hCY⟩ :=
    M.chart_finitePL.exists_collar_base_restriction M.width_pos
      (fun x hx => (M.upper_bounds x hx).2) hbB Kb hKb hKbs
  obtain ⟨hXs, hYs, hsplit, hdisj, hdcap⟩ :=
    M.ordinary_collar_decomposition hs hs' hunion hinter hB htouch hcap
      hselected hTX hTY hCX hCY
  have hCheight : ∀ p, A (C p) = (p : E × ℝ).2 := by
    intro p
    rw [hCval]
    exact M.height _
  have hCcontact : ∀ p, (C p : E) ∈ M.residual ↔
      (p : E × ℝ).2 = M.upper (p : E × ℝ).1 := by
    intro p
    rw [hCval]
    exact M.roof_contact _
  have hcopy := hC.symm
  obtain ⟨_, ⟨KT, hKT, hKTs, _⟩, _⟩ := hcopy
  have hgT : FinitePiecewiseAffineOn g TX :=
    hKTs ▸ hg.restrict KT hKT (hKTs.subset.trans hTX)
  have hgbottom (p : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (M.upper p.1)})
      (hp : (p : E × ℝ).2 = 0) : g (C p) = 0 := by
    rw [hCval, M.bottom _ hp]
    exact hgN _ p.property.1.1
  obtain ⟨δ, hδ, hcoords⟩ := hC.exists_moved_collar_height_coordinates_with_endpoints
    (fun x hx => (M.upper_bounds x (hXB hx)).1) A hCheight hCcontact hgT
    hgbottom (fun p hp => hgR _ ((hCcontact p).mpr hp)) v hv
  refine ⟨TX, TY, hTX, hTY, hXs, hYs, hsplit, hdisj, hdcap, hCX, hCY,
    δ, hδ, fun t ht H hglobal hformula => ?_⟩
  obtain ⟨D, hD, hDheight, hDfix, hDcontact⟩ := hcoords t ht H
    (hKTs ▸ hglobal KT hKT) (fun x _ => hformula x)
  have hfixR (x : E) (hx : x ∈ M.residual) : H x = x := by
    rw [hformula, hgR x hx, mul_zero, zero_smul, add_zero]
  have himageR : H '' M.residual = M.residual := by
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
  exact ⟨F, hF, hFA, hFR, hFT, hFRmem⟩

end Geometry
