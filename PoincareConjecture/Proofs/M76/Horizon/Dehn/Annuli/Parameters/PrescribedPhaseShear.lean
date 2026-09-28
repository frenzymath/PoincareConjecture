import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusPLLift

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_annulus_prescribed_phase_shear {L d a₀ a₁ : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L)
    (ha₀ : a₀ ∈ Icc 0 (4 * L)) (ha₁ : a₁ ∈ Icc 0 (4 * L)) :
    ∃ A : squareAnnulus L d ≃ₜ squareAnnulus L d, A.IsFinitePL ∧
      (∀ z, depth L (A z) = depth L z) ∧
      ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        (A ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩ : P2) =
        annulusMap L (by linarith)
          ((((s + (a₀ + a₁) / 2 + (a₁ - a₀) / (2 * d) * (u : ℝ) : ℝ) :
            AddCircle (4 * L))), u) := by
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨mul_pos (by norm_num) hL⟩
  let shift : ℝ → ℝ := fun u ↦ (a₀ + a₁) / 2 + (a₁ - a₀) / (2 * d) * u
  let B : P2 →ᴬ[ℝ] P2 :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap +
      (ContinuousAffineMap.const ℝ P2 ((a₀ + a₁) / 2) +
        ((a₁ - a₀) / (2 * d)) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hB (x : P2) : B x = (x.1 + shift x.2, x.2) := rfl
  have hshift {u : ℝ} (hu : u ∈ Icc (-d) d) : 0 ≤ shift u ∧ shift u ≤ 4 * L := by
    have h₀ : 0 ≤ d - u := by linarith [hu.2]
    have h₁ : 0 ≤ d + u := by linarith [hu.1]
    have heq : 2 * d * shift u = (d - u) * a₀ + (d + u) * a₁ := by
      dsimp [shift]
      field_simp
      ring
    have hlo := add_nonneg (mul_nonneg h₀ ha₀.1) (mul_nonneg h₁ ha₁.1)
    have hhi := add_le_add (mul_le_mul_of_nonneg_left ha₀.2 h₀)
      (mul_le_mul_of_nonneg_left ha₁.2 h₁)
    constructor <;> nlinarith
  have hmaps : MapsTo B (rectangle (4 * L) d)
      (Icc (4 * L - 4 * L) (4 * L + 4 * L) ×ˢ Icc (-d) d) := by
    intro x hx
    rw [hB]
    exact ⟨⟨by dsimp; linarith [hx.1.1, (hshift hx.2).1],
      by dsimp; linarith [hx.1.2, (hshift hx.2).2]⟩, hx.2⟩
  have hBPL : FinitePiecewiseAffineOn B (rectangle (4 * L) d) := by
    obtain ⟨K, hK, hKs, _⟩ := finitePiecewiseAffineOn_wrappedStripMap hd hwidth
    exact ⟨K, hK, hKs, K.affineOnFaces_affine B⟩
  let phi : P2 → P2 := fun x ↦
    annulusMap L hL (((x.1 + shift x.2 : ℝ) : AddCircle (4 * L)), x.2)
  have hphi : FinitePiecewiseAffineOn phi (rectangle (4 * L) d) :=
    (finitePiecewiseAffineOn_annulusMap_twoPeriods hL hd hwidth
      (c := 4 * L) (AddCircle.coe_period _)).comp hBPL hmaps
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
    · rintro _ ⟨x, hx, rfl⟩
      exact _root_.Dehn.annulus_period_point_mem hd hwidth _ ⟨x.2, hx.2⟩
    · intro z hz
      obtain ⟨s, hs, hsz⟩ := exists_period_parameter_of_depth hd hwidth ⟨z, hz⟩
      let u := depth L z
      have hu : u ∈ Icc (-d) d := mem_squareAnnulus_iff_depth.mp hz
      let v : ℝ := AddCircle.equivIco (4 * L) 0
        ((s : AddCircle (4 * L)) - (shift u : AddCircle (4 * L)))
      have hv : v ∈ Icc 0 (4 * L) :=
        ⟨(AddCircle.equivIco (4 * L) 0 _).property.1,
          by simpa only [zero_add] using (AddCircle.equivIco (4 * L) 0
            ((s : AddCircle (4 * L)) - (shift u : AddCircle (4 * L)))).property.2.le⟩
      have hvcoe : (v : AddCircle (4 * L)) =
          (s : AddCircle (4 * L)) - (shift u : AddCircle (4 * L)) := AddCircle.coe_equivIco
      refine ⟨(v, u), ⟨hv, hu⟩, ?_⟩
      change annulusMap L hL ((((v + shift u : ℝ) : AddCircle (4 * L))), u) = z
      rw [AddCircle.coe_add, hvcoe, sub_add_cancel]
      exact hsz.symm
  obtain ⟨A, hA, _, hperiod, hpoint⟩ :=
    _root_.Dehn.exists_finitePL_annulus_of_periodic_strip hd hwidth phi hphi hfib
  refine ⟨A.trans (Homeomorph.setCongr himage), hA.setCongr rfl himage, ?_, ?_⟩
  · intro z
    obtain ⟨s, hs, hsz⟩ := exists_period_parameter_of_depth hd hwidth z
    change depth L (A z) = depth L z
    rw [hpoint z s hs hsz]
    exact depth_annulusMap hL
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (abs_le.mpr (mem_squareAnnulus_iff_depth.mp z.property)) (by norm_num)) hwidth) _
  · intro s hs u
    exact (hperiod s hs u).trans (by simp only [phi, shift, add_assoc])

end PoincareConjecture.M76.Dehn
