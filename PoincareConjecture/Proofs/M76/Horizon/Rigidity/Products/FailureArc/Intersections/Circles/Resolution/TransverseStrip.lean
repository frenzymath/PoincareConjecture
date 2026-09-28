import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.IdentityAnnulus



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

noncomputable def capStrip (d ε : ℝ) (p : P2) : C3 :=
  (((1 - ε / (2 * d)) * p.2 - ε / 2, d), p.1)

theorem capStrip_first_bounds {L d ε : ℝ} (hd : 0 < d) (hε : 0 ≤ ε)
    (hεd : ε < 2 * d) {p : P2} (hp : p ∈ rectangle (4 * L) d) :
    -d ≤ (capStrip d ε p).1.1 ∧ (capStrip d ε p).1.1 ≤ d - ε := by
  have hcoef : 0 < 1 - ε / (2 * d) := by
    have hh := (div_lt_one (by positivity : 0 < 2 * d)).mpr hεd
    linarith
  have hmul : (ε / (2 * d)) * d = ε / 2 := by field_simp
  change -d ≤ (1 - ε / (2 * d)) * p.2 - ε / 2 ∧
    (1 - ε / (2 * d)) * p.2 - ε / 2 ≤ d - ε
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hp.2.1 hcoef.le,
    mul_le_mul_of_nonneg_left hp.2.2 hcoef.le]

theorem capStrip_mapsTo {L d ε : ℝ} (hd : 0 < d) (hε : 0 ≤ ε) (hεd : ε < 2 * d) :
    MapsTo (capStrip d ε) (rectangle (4 * L) d) (_root_.Dehn.identityTube L d) := by
  intro p hp
  have h := capStrip_first_bounds hd hε hεd hp
  exact ⟨⟨⟨h.1, by linarith [h.2]⟩, ⟨by change -d ≤ d; linarith, le_rfl⟩⟩, hp.1⟩

theorem capStrip_avoids_diagonal {L d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hεd : ε < 2 * d) {p : P2} (hp : p ∈ rectangle (4 * L) d) :
    (capStrip d ε p).1.1 < (capStrip d ε p).1.2 := by
  have h := (capStrip_first_bounds hd hε.le hεd hp).2
  change _ < d
  linarith

theorem capStrip_outer (d ε t : ℝ) (hd : d ≠ 0) :
    capStrip d ε (t, -d) = ((-d, d), t) := by
  simp only [capStrip, Prod.mk.injEq, and_true]
  field_simp
  ring

theorem capStrip_inner (d ε t : ℝ) (hd : d ≠ 0) :
    capStrip d ε (t, d) = ((d - ε, d), t) := by
  simp only [capStrip, Prod.mk.injEq, and_true]
  field_simp
  ring

theorem capStrip_antidiagonal_iff {d ε : ℝ} (hd : 0 < d) (hεd : ε < 2 * d) (p : P2) :
    (capStrip d ε p).1.2 = -(capStrip d ε p).1.1 ↔ p.2 = -d := by
  have hcoef : 0 < 1 - ε / (2 * d) := by
    have hh := (div_lt_one (by positivity : 0 < 2 * d)).mpr hεd
    linarith
  have hmul : (ε / (2 * d)) * d = ε / 2 := by field_simp
  change d = -((1 - ε / (2 * d)) * p.2 - ε / 2) ↔ p.2 = -d
  constructor
  · intro h
    have he : (1 - ε / (2 * d)) * (p.2 + d) = 0 := by nlinarith
    have hh := (mul_eq_zero.mp he).resolve_left hcoef.ne'
    linarith
  · intro h
    rw [h]
    nlinarith

theorem capStrip_transverse_injective {d ε : ℝ} (hd : 0 < d) (hεd : ε < 2 * d)
    {p q : P2} (h : (capStrip d ε p).1 = (capStrip d ε q).1) : p.2 = q.2 := by
  have hcoef : 0 < 1 - ε / (2 * d) := by
    have hh := (div_lt_one (by positivity : 0 < 2 * d)).mpr hεd
    linarith
  have hh := congrArg Prod.fst h
  change (1 - ε / (2 * d)) * p.2 - ε / 2 =
    (1 - ε / (2 * d)) * q.2 - ε / 2 at hh
  exact mul_left_cancel₀ hcoef.ne' (sub_left_injective hh)

theorem capStrip_finitePL {L d : ℝ} (hd : 0 < d) (hL : 0 < L) (ε : ℝ) :
    FinitePiecewiseAffineOn (capStrip d ε) (rectangle (4 * L) d) := by
  have hrect := (isFinitePLBallPair_Icc (show (0 : ℝ) < 4 * L by linarith)).prod
    (isFinitePLBallPair_Icc (show -d < d by linarith))
  obtain ⟨_, _, _, _, _, c, hc, _⟩ := hrect
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hc
  let a : P2 →ᴬ[ℝ] ℝ :=
    (1 - ε / (2 * d)) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap -
      ContinuousAffineMap.const ℝ P2 (ε / 2)
  let b : P2 →ᴬ[ℝ] C3 :=
    (a.prod (ContinuousAffineMap.const ℝ P2 d)).prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  exact ⟨K, hK, hKs, K.affineOnFaces_affine b⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
