import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.CyclicStripMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondSquareCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.ClosedPeriodCut

set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

private theorem sheet_zero_iff (x : P2) :
    x ∈ signedTubeSheet 0 ↔ x.1 = 0 ∧ x.2 ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · rintro (hx | hx)
    all_goals
      obtain ⟨a, b, ha, hb, hab, hval⟩ := hx
      have hfst := congrArg Prod.fst hval
      have hsnd := congrArg Prod.snd hval
      norm_num [signedTubeCorner] at hfst hsnd
      exact ⟨hfst.symm, by constructor <;> linarith⟩
  · rintro ⟨hx, hy⟩
    have hd : x ∈ signedTubeDiamond := by
      rw [signedTubeDiamond_coordinate_iff, hx]
      simpa using abs_le.mpr hy
    exact (signedTubeSheet_coordinate_iff x hd 0).mpr hx

private noncomputable def stripAnnulusCoordinates (n : ℕ) : P2 →L[ℝ] P2 × ℝ :=
  ((0 : P2 →L[ℝ] ℝ).prod ((8 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    ((((n : ℝ) + 3) / 4) • ContinuousLinearMap.fst ℝ ℝ ℝ)

private theorem stripAnnulusCoordinates_apply (n : ℕ) (x : P2) :
    stripAnnulusCoordinates n x = ((0, 8 * x.2), ((n : ℝ) + 3) / 4 * x.1) := rfl

private theorem stripAnnulusCoordinates_mem (n : ℕ) {x : P2}
    (hx : x ∈ rectangle (4 : ℝ) (1 / 8)) :
    stripAnnulusCoordinates n x ∈ signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3) := by
  have hn : 0 < (n : ℝ) + 3 := by positivity
  rw [stripAnnulusCoordinates_apply]
  refine ⟨(sheet_zero_iff _).mpr ⟨rfl, ?_⟩, ?_⟩
  · constructor <;> linarith [hx.2.1, hx.2.2]
  · constructor <;> nlinarith [hx.1.1, hx.1.2]

private theorem stripAnnulusCoordinates_image (n : ℕ) :
    stripAnnulusCoordinates n '' rectangle (4 : ℝ) (1 / 8) =
      signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3) := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact stripAnnulusCoordinates_mem n hx
  · rintro ⟨⟨x, y⟩, t⟩ ⟨hxy, ht⟩
    obtain ⟨rfl, hy⟩ := (sheet_zero_iff _).mp hxy
    have hn : 0 < (n : ℝ) + 3 := by positivity
    refine ⟨(4 * t / ((n : ℝ) + 3), y / 8), ⟨?_, ?_⟩, ?_⟩
    · constructor
      · exact div_nonneg (mul_nonneg (by norm_num) ht.1) hn.le
      · apply (div_le_iff₀ hn).mpr
        nlinarith [ht.2]
    · constructor <;> linarith [hy.1, hy.2]
    · rw [stripAnnulusCoordinates_apply]
      dsimp
      congr 1
      · congr 1
        ring
      · field_simp

private theorem stripAnnulusCoordinates_finitePL (n : ℕ) :
    FinitePiecewiseAffineOn (stripAnnulusCoordinates n) (rectangle (4 : ℝ) (1 / 8)) := by
  have hrect := (isFinitePLBallPair_Icc (show (0 : ℝ) < 4 by norm_num)).prod
    (isFinitePLBallPair_Icc (show -(1 / 8 : ℝ) < 1 / 8 by norm_num))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hrect
  exact ⟨K, hK, hKs, K.affineOnFaces_affine
    (stripAnnulusCoordinates n).toContinuousAffineMap⟩

theorem exists_annulus_of_cyclic_strip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (sigma : P2 × ℝ → E)
    (hPL : FinitePiecewiseAffineOn sigma (signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3)))
    (hfib : ∀ x y : ↥(signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3)),
      sigma x = sigma y ↔ x = y ∨
        ((x : P2 × ℝ).2 = 0 ∧ (y : P2 × ℝ).2 = n + 3 ∧
          (x : P2 × ℝ).1 = (y : P2 × ℝ).1) ∨
        ((y : P2 × ℝ).2 = 0 ∧ (x : P2 × ℝ).2 = n + 3 ∧
          (y : P2 × ℝ).1 = (x : P2 × ℝ).1))
    (Z : Set E)
    (haxis : ∀ x ∈ signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3),
      sigma x ∈ Z ↔ x.1 = (0, 0)) :
    ∃ c : squareAnnulus 1 (1 / 8) ≃ₜ
        (sigma '' (signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3))),
      c.IsFinitePL ∧ c.symm.IsFinitePL ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 4) (u : Icc (-(1 / 8 : ℝ)) (1 / 8)),
        (c ⟨annulusMap 1 (by norm_num) ((s : AddCircle (4 * (1 : ℝ))), u),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : E) =
          sigma ((0, 8 * (u : ℝ)), ((n : ℝ) + 3) / 4 * s)) ∧
      ∀ p : squareAnnulus 1 (1 / 8), (c p : E) ∈ Z ↔ depth 1 p = 0 := by
  let φ : P2 → E := sigma ∘ stripAnnulusCoordinates n
  have hφ : FinitePiecewiseAffineOn φ (rectangle (4 : ℝ) (1 / 8)) :=
    hPL.comp (stripAnnulusCoordinates_finitePL n) (fun _ ↦ stripAnnulusCoordinates_mem n)
  let : Fact (0 < 4 * (1 : ℝ)) := ⟨by norm_num⟩
  have hn : 0 < (n : ℝ) + 3 := by positivity
  have hφfib : ∀ x ∈ rectangle (4 : ℝ) (1 / 8),
      ∀ y ∈ rectangle (4 : ℝ) (1 / 8),
      φ x = φ y ↔ x.2 = y.2 ∧
        (x.1 : AddCircle (4 * (1 : ℝ))) = (y.1 : AddCircle (4 * (1 : ℝ))) := by
    intro x hx y hy
    rw [AddCircle.coe_eq_coe_iff_eq_or_endpoints
      (show x.1 ∈ Icc 0 (4 * (1 : ℝ)) by simpa only [mul_one] using hx.1)
      (show y.1 ∈ Icc 0 (4 * (1 : ℝ)) by simpa only [mul_one] using hy.1)]
    have hh := hfib ⟨_, stripAnnulusCoordinates_mem n hx⟩
      ⟨_, stripAnnulusCoordinates_mem n hy⟩
    change φ x = φ y ↔ _ at hh
    rw [hh]
    simp only [Subtype.ext_iff, stripAnnulusCoordinates_apply, Prod.mk.injEq] at *
    constructor
    · rintro (⟨⟨_, hu⟩, hs⟩ | ⟨hs, ht, _, hu⟩ | ⟨ht, hs, _, hu⟩)
      · exact ⟨by linarith, Or.inl (by nlinarith)⟩
      · exact ⟨by linarith, Or.inr (Or.inl ⟨by nlinarith, by nlinarith⟩)⟩
      · exact ⟨by linarith, Or.inr (Or.inr ⟨by nlinarith, by nlinarith⟩)⟩
    · rintro ⟨hu, hs | ⟨hs, ht⟩ | ⟨hs, ht⟩⟩
      · exact Or.inl ⟨⟨trivial, congrArg (8 * ·) hu⟩,
          congrArg (((n : ℝ) + 3) / 4 * ·) hs⟩
      · right; left
        simp [hs, ht, hu]
      · right; right
        simp [hs, ht, hu]
  obtain ⟨c, hc, hci, hperiod, hdepth⟩ :=
    _root_.Dehn.exists_finitePL_annulus_of_periodic_strip
      (L := 1) (d := 1 / 8) (by norm_num) (by norm_num) φ
      (by simpa only [mul_one] using hφ) (by simpa only [mul_one] using hφfib)
  have himage : φ '' rectangle (4 : ℝ) (1 / 8) =
      sigma '' (signedTubeSheet 0 ×ˢ Icc (0 : ℝ) (n + 3)) := by
    rw [show φ = sigma ∘ stripAnnulusCoordinates n from rfl, image_comp,
      stripAnnulusCoordinates_image]
  let c' := c.trans (Homeomorph.setCongr (by simpa only [mul_one] using himage))
  have hc' : c'.IsFinitePL := by
    obtain ⟨f, hf, hval⟩ := hc
    exact ⟨f, hf, hval⟩
  refine ⟨c', hc', hc'.symm, ?_, ?_⟩
  · intro s hs u
    exact hperiod s (by simpa only [mul_one] using hs) u
  · intro p
    obtain ⟨s, hs, hp⟩ := exists_period_parameter_of_depth
      (show (0 : ℝ) < 1 / 8 by norm_num) (show 4 * (1 / 8 : ℝ) < 1 by norm_num) p
    have hu := mem_squareAnnulus_iff_depth.mp p.property
    change (c p : E) ∈ Z ↔ _
    rw [hdepth p s hs hp]
    change sigma (stripAnnulusCoordinates n (s, depth 1 p)) ∈ Z ↔ _
    rw [haxis _ (stripAnnulusCoordinates_mem n
      ⟨by simpa only [mul_one] using hs, hu⟩)]
    simp [stripAnnulusCoordinates_apply]

end PoincareConjecture.M76.Dehn
