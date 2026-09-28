import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusPLLift










set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_square_annulus_half_period_shear {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ c : squareAnnulus L d ≃ₜ squareAnnulus L d,
      c.IsFinitePL ∧ c.symm.IsFinitePL ∧
      (∀ p, depth L (c p) = depth L p) ∧
      ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        (c ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          annulus_period_point_mem hd hwidth _ u⟩ : P2) =
          annulusMap L (by linarith)
            (((s + (L - (L / d) * u) : ℝ) : AddCircle (4 * L)), u) := by
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨by positivity⟩
  let shift : ℝ → ℝ := fun u ↦ L - (L / d) * u
  let A : P2 →ᴬ[ℝ] P2 :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap +
      (ContinuousAffineMap.const ℝ P2 L -
        (L / d) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hA (x : P2) : A x = (x.1 + shift x.2, x.2) := rfl
  have hshift {u : ℝ} (hu : u ∈ Icc (-d) d) : 0 ≤ shift u ∧ shift u ≤ 2 * L := by
    have hpos : 0 ≤ L / d := (div_pos hL hd).le
    have hlo := mul_le_mul_of_nonneg_left hu.1 hpos
    have hhi := mul_le_mul_of_nonneg_left hu.2 hpos
    rw [mul_neg, div_mul_cancel₀ _ hd.ne'] at hlo
    rw [div_mul_cancel₀ _ hd.ne'] at hhi
    dsimp [shift]
    constructor <;> linarith
  have hmaps : MapsTo A (rectangle (4 * L) d)
      (Icc (4 * L - 4 * L) (4 * L + 4 * L) ×ˢ Icc (-d) d) := by
    intro x hx
    rw [hA]
    exact ⟨⟨by dsimp; linarith [hx.1.1, (hshift hx.2).1],
      by dsimp; linarith [hx.1.2, (hshift hx.2).2]⟩, hx.2⟩
  have hAPL : FinitePiecewiseAffineOn A (rectangle (4 * L) d) := by
    obtain ⟨K, hK, hKs, _⟩ := finitePiecewiseAffineOn_wrappedStripMap hd hwidth
    exact ⟨K, hK, hKs, K.affineOnFaces_affine A⟩
  let phi : P2 → P2 := fun x ↦
    annulusMap L hL (((x.1 + shift x.2 : ℝ) : AddCircle (4 * L)), x.2)
  have hphi : FinitePiecewiseAffineOn phi (rectangle (4 * L) d) :=
    (finitePiecewiseAffineOn_annulusMap_twoPeriods hL hd hwidth
      (c := 4 * L) (AddCircle.coe_period _)).comp hAPL hmaps
  have hfib : ∀ x ∈ rectangle (4 * L) d, ∀ y ∈ rectangle (4 * L) d,
      phi x = phi y ↔ x.2 = y.2 ∧
        (x.1 : AddCircle (4 * L)) = (y.1 : AddCircle (4 * L)) := by
    intro x hx y hy
    constructor
    · intro h
      have heq := injective_annulusMap hL hwidth
        (a₁ := (((x.1 + shift x.2 : ℝ) : AddCircle (4 * L)), ⟨x.2, hx.2⟩))
        (a₂ := (((y.1 + shift y.2 : ℝ) : AddCircle (4 * L)), ⟨y.2, hy.2⟩)) h
      have hu : x.2 = y.2 := congrArg (fun z ↦ (z.2 : ℝ)) heq
      have hs := congrArg Prod.fst heq
      change ((x.1 + shift x.2 : ℝ) : AddCircle (4 * L)) =
        ((y.1 + shift y.2 : ℝ) : AddCircle (4 * L)) at hs
      simp only [hu, AddCircle.coe_add] at hs
      exact ⟨hu, add_right_cancel hs⟩
    · rintro ⟨hu, hs⟩
      dsimp [phi]
      simp only [hu, hs]
  have himage : phi '' rectangle (4 * L) d = squareAnnulus L d := by
    apply Subset.antisymm
    · rintro p ⟨x, hx, rfl⟩
      exact annulus_period_point_mem hd hwidth _ ⟨x.2, hx.2⟩
    · intro p hp
      obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth ⟨p, hp⟩
      let u := depth L p
      have hu : u ∈ Icc (-d) d := mem_squareAnnulus_iff_depth.mp hp
      let v : ℝ := AddCircle.equivIco (4 * L) 0
        ((s : AddCircle (4 * L)) - (shift u : AddCircle (4 * L)))
      have hv : v ∈ Icc 0 (4 * L) :=
        ⟨(AddCircle.equivIco (4 * L) 0 _).property.1,
          by simpa only [zero_add] using (AddCircle.equivIco (4 * L) 0
            ((s : AddCircle (4 * L)) - (shift u : AddCircle (4 * L)))).property.2.le⟩
      have hvcoe : (v : AddCircle (4 * L)) =
          (s : AddCircle (4 * L)) - (shift u : AddCircle (4 * L)) :=
        AddCircle.coe_equivIco
      refine ⟨(v, u), ⟨hv, hu⟩, ?_⟩
      change annulusMap L hL ((((v + shift u : ℝ) : AddCircle (4 * L))), u) = p
      rw [AddCircle.coe_add, hvcoe, sub_add_cancel]
      exact hsp.symm
  obtain ⟨b, hb, _hbi, hperiod, hpoint⟩ :=
    exists_finitePL_annulus_of_periodic_strip hd hwidth phi hphi hfib
  let c := b.trans (Homeomorph.setCongr himage)
  have hc : c.IsFinitePL := by
    obtain ⟨g, hg, hgval⟩ := hb
    exact ⟨g, hg, hgval⟩
  refine ⟨c, hc, hc.symm, ?_, hperiod⟩
  intro p
  obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
  change depth L (b p) = depth L p
  rw [hpoint p s hs hsp]
  exact depth_annulusMap hL
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (abs_le.mpr (mem_squareAnnulus_iff_depth.mp p.property)) (by norm_num)) hwidth) _

end Dehn
