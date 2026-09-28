import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusPLLift








set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_annulus_period_reflection {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ A : squareAnnulus L d ≃ₜ squareAnnulus L d, A.IsFinitePL ∧
      ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        (A ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          _root_.Dehn.annulus_period_point_mem hd hwidth _ u⟩ : P2) =
        annulusMap L (by linarith) (-((s : ℝ) : AddCircle (4 * L)), u) := by
  have hL : 0 < L := by linarith
  let : Fact (0 < 4 * L) := ⟨mul_pos (by norm_num) hL⟩
  let B : P2 →ᴬ[ℝ] P2 :=
    (ContinuousAffineMap.const ℝ P2 (4 * L) -
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hB (x : P2) : B x = (4 * L - x.1, x.2) := rfl
  have hmaps : MapsTo B (rectangle (4 * L) d) (rectangle (4 * L) d) := by
    intro x hx
    exact ⟨⟨by change 0 ≤ 4 * L - x.1; linarith [hx.1.2],
      by change 4 * L - x.1 ≤ 4 * L; linarith [hx.1.1]⟩, hx.2⟩
  have hBPL : FinitePiecewiseAffineOn B (rectangle (4 * L) d) := by
    obtain ⟨K, hK, hKs, _⟩ := finitePiecewiseAffineOn_wrappedStripMap hd hwidth
    exact ⟨K, hK, hKs, K.affineOnFaces_affine B⟩
  let phi : P2 → P2 := fun x ↦ annulusMap L hL (-((x.1 : ℝ) : AddCircle (4 * L)), x.2)
  have hperiodPL : FinitePiecewiseAffineOn
      (fun x : P2 ↦ annulusMap L hL ((x.1 : AddCircle (4 * L)), x.2))
      (rectangle (4 * L) d) := by
    simpa only [zero_add, rectangle] using finitePiecewiseAffineOn_annulusMap_period
      hL hd hwidth (c := 0) (AddCircle.coe_zero _)
  have hphi : FinitePiecewiseAffineOn phi (rectangle (4 * L) d) :=
    (hperiodPL.comp hBPL hmaps).congr (by
      intro x _
      change annulusMap L hL (((4 * L - x.1 : ℝ) : AddCircle (4 * L)), x.2) = _
      simp only [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, phi])
  have hfib : ∀ x ∈ rectangle (4 * L) d, ∀ y ∈ rectangle (4 * L) d,
      phi x = phi y ↔ x.2 = y.2 ∧
        (x.1 : AddCircle (4 * L)) = (y.1 : AddCircle (4 * L)) := by
    intro x hx y hy
    constructor
    · intro h
      have hh := injective_annulusMap hL hwidth
        (a₁ := (-((x.1 : ℝ) : AddCircle (4 * L)), ⟨x.2, hx.2⟩))
        (a₂ := (-((y.1 : ℝ) : AddCircle (4 * L)), ⟨y.2, hy.2⟩)) h
      exact ⟨congrArg (fun z ↦ (z.2 : ℝ)) hh, neg_injective (congrArg Prod.fst hh)⟩
    · rintro ⟨hu, hs⟩
      simp only [phi, hu, hs]
  have himage : phi '' rectangle (4 * L) d = squareAnnulus L d := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact _root_.Dehn.annulus_period_point_mem hd hwidth _ ⟨x.2, hx.2⟩
    · intro z hz
      obtain ⟨s, hs, hsz⟩ := exists_period_parameter_of_depth hd hwidth ⟨z, hz⟩
      have hu := mem_squareAnnulus_iff_depth.mp hz
      refine ⟨(4 * L - s, depth L z), ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, hu⟩, ?_⟩
      change annulusMap L hL (-((4 * L - s : ℝ) : AddCircle (4 * L)), depth L z) = z
      simp only [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, neg_neg]
      exact hsz.symm
  obtain ⟨A, hA, _, hperiod, _⟩ :=
    _root_.Dehn.exists_finitePL_annulus_of_periodic_strip hd hwidth phi hphi hfib
  exact ⟨A.trans (Homeomorph.setCongr himage), hA.setCongr rfl himage, hperiod⟩

end PoincareConjecture.M76.Dehn
