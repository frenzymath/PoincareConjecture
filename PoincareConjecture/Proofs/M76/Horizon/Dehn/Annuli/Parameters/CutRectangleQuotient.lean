import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusPLLift
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_annulus_homeomorph_of_cut_rectangle {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L)
    (H : rectangle (4 * L) d ≃ₜ rectangle (4 * L) d) (hH : H.IsFinitePL)
    (hleft : ∀ u : Icc (-d) d,
      (H ⟨(0, u), ⟨by constructor <;> linarith, u.property⟩⟩ : P2) = (0, (u : ℝ)))
    (hright : ∀ u : Icc (-d) d,
      (H ⟨(4 * L, u), ⟨by constructor <;> linarith, u.property⟩⟩ : P2) = (4 * L, (u : ℝ))) :
    ∃ A : squareAnnulus L d ≃ₜ squareAnnulus L d, A.IsFinitePL ∧
      ∀ (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        (A ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩ : P2) =
        annulusMap L (by linarith)
          (((H ⟨(s, u), hs, u.property⟩ : P2).1 : AddCircle (4 * L)),
            (H ⟨(s, u), hs, u.property⟩ : P2).2) := by
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨mul_pos (by norm_num) hL⟩
  obtain ⟨g, hg, hgval⟩ := hH
  have hgm : MapsTo g (rectangle (4 * L) d) (rectangle (4 * L) d) := by
    intro x hx
    rw [← hgval ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  let q : P2 → P2 := fun x ↦ annulusMap L hL ((x.1 : AddCircle (4 * L)), x.2)
  have hq : FinitePiecewiseAffineOn q (rectangle (4 * L) d) := by
    simpa only [q, rectangle, zero_add] using finitePiecewiseAffineOn_annulusMap_period hL hd hwidth
      (c := 0) (AddCircle.coe_zero _)
  let phi := q ∘ g
  have hphi : FinitePiecewiseAffineOn phi (rectangle (4 * L) d) := hq.comp hg hgm
  have hzero (z : rectangle (4 * L) d) (hz : (H z : P2).1 = 0) :
      (z : P2) = (0, (H z : P2).2) := by
    have hh : H z = H ⟨(0, (H z : P2).2),
        ⟨⟨le_rfl, by linarith⟩, (H z).property.2⟩⟩ := by
      apply Subtype.ext
      rw [hleft ⟨(H z : P2).2, (H z).property.2⟩]
      exact Prod.ext hz rfl
    exact congrArg Subtype.val (H.injective hh)
  have hone (z : rectangle (4 * L) d) (hz : (H z : P2).1 = 4 * L) :
      (z : P2) = (4 * L, (H z : P2).2) := by
    have hh : H z = H ⟨(4 * L, (H z : P2).2),
        ⟨⟨by linarith, le_rfl⟩, (H z).property.2⟩⟩ := by
      apply Subtype.ext
      rw [hright ⟨(H z : P2).2, (H z).property.2⟩]
      exact Prod.ext hz rfl
    exact congrArg Subtype.val (H.injective hh)
  have hfib : ∀ x ∈ rectangle (4 * L) d, ∀ y ∈ rectangle (4 * L) d,
      phi x = phi y ↔ x.2 = y.2 ∧
        (x.1 : AddCircle (4 * L)) = (y.1 : AddCircle (4 * L)) := by
    intro x hx y hy
    change q (g x) = q (g y) ↔ _
    rw [← hgval ⟨x, hx⟩, ← hgval ⟨y, hy⟩]
    constructor
    · intro heq
      have hh := injective_annulusMap hL hwidth
        (a₁ := (((H ⟨x, hx⟩ : P2).1 : AddCircle (4 * L)),
          ⟨(H ⟨x, hx⟩ : P2).2, (H ⟨x, hx⟩).property.2⟩))
        (a₂ := (((H ⟨y, hy⟩ : P2).1 : AddCircle (4 * L)),
          ⟨(H ⟨y, hy⟩ : P2).2, (H ⟨y, hy⟩).property.2⟩)) heq
      have ht := congrArg (fun z : AddCircle (4 * L) × Icc (-d) d ↦ (z.2 : ℝ)) hh
      have hs := congrArg Prod.fst hh
      rcases (AddCircle.coe_eq_coe_iff_eq_or_endpoints
        (H ⟨x, hx⟩).property.1 (H ⟨y, hy⟩).property.1).mp hs with hs | hs | hs
      · have hxy : x = y := congrArg Subtype.val
          (H.injective (Subtype.ext (Prod.ext hs ht)))
        rw [hxy]
        exact ⟨rfl, rfl⟩
      · have hx' := hzero ⟨x, hx⟩ hs.1
        have hy' := hone ⟨y, hy⟩ hs.2
        exact ⟨(congrArg Prod.snd hx').trans (ht.trans (congrArg Prod.snd hy').symm),
          by rw [congrArg Prod.fst hx', congrArg Prod.fst hy'];
             exact (AddCircle.coe_zero _).trans (AddCircle.coe_period _).symm⟩
      · have hx' := hone ⟨x, hx⟩ hs.1
        have hy' := hzero ⟨y, hy⟩ hs.2
        exact ⟨(congrArg Prod.snd hx').trans (ht.trans (congrArg Prod.snd hy').symm),
          by rw [congrArg Prod.fst hx', congrArg Prod.fst hy'];
             exact (AddCircle.coe_period _).trans (AddCircle.coe_zero _).symm⟩
    · rintro ⟨ht, hs⟩
      rcases (AddCircle.coe_eq_coe_iff_eq_or_endpoints hx.1 hy.1).mp hs with hs | hs | hs
      · have hxy : x = y := Prod.ext hs ht
        subst y
        rfl
      · have hx' : (⟨x, hx⟩ : rectangle (4 * L) d) =
            ⟨(0, x.2), ⟨⟨le_rfl, by linarith⟩, hx.2⟩⟩ := Subtype.ext (Prod.ext hs.1 rfl)
        have hy' : (⟨y, hy⟩ : rectangle (4 * L) d) =
            ⟨(4 * L, y.2), ⟨⟨by linarith, le_rfl⟩, hy.2⟩⟩ := Subtype.ext (Prod.ext hs.2 rfl)
        rw [hx', hy', hleft ⟨x.2, hx.2⟩, hright ⟨y.2, hy.2⟩]
        change annulusMap L hL ((0 : ℝ), x.2) =
          annulusMap L hL (((4 * L : ℝ) : AddCircle (4 * L)), y.2)
        rw [AddCircle.coe_period, ht]
        rfl
      · have hx' : (⟨x, hx⟩ : rectangle (4 * L) d) =
            ⟨(4 * L, x.2), ⟨⟨by linarith, le_rfl⟩, hx.2⟩⟩ := Subtype.ext (Prod.ext hs.1 rfl)
        have hy' : (⟨y, hy⟩ : rectangle (4 * L) d) =
            ⟨(0, y.2), ⟨⟨le_rfl, by linarith⟩, hy.2⟩⟩ := Subtype.ext (Prod.ext hs.2 rfl)
        rw [hx', hy', hright ⟨x.2, hx.2⟩, hleft ⟨y.2, hy.2⟩]
        change annulusMap L hL ((((4 * L : ℝ) : AddCircle (4 * L)), x.2)) =
          annulusMap L hL ((0 : ℝ), y.2)
        rw [AddCircle.coe_period, ht]
        rfl
  have himage : phi '' rectangle (4 * L) d = squareAnnulus L d := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact _root_.Dehn.annulus_period_point_mem hd hwidth _ ⟨(g x).2, (hgm hx).2⟩
    · intro z hz
      obtain ⟨s, hs, hsz⟩ := exists_period_parameter_of_depth hd hwidth ⟨z, hz⟩
      have hu := mem_squareAnnulus_iff_depth.mp hz
      let y : rectangle (4 * L) d := ⟨(s, depth L z), hs, hu⟩
      refine ⟨H.symm y, (H.symm y).property, ?_⟩
      change q (g (H.symm y)) = z
      rw [← hgval, H.apply_symm_apply]
      exact hsz.symm
  obtain ⟨A, hA, _, hperiod, _⟩ :=
    _root_.Dehn.exists_finitePL_annulus_of_periodic_strip hd hwidth phi hphi hfib
  refine ⟨A.trans (Homeomorph.setCongr himage), hA.setCongr rfl himage, ?_⟩
  intro s hs u
  exact (hperiod s hs u).trans (congrArg q (hgval ⟨(s, u), hs, u.property⟩).symm)

end PoincareConjecture.M76.Dehn
