import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace CoordinateHalfBoxes

noncomputable def longitudinalPrismCoordinates (r a b : ℝ) :
    ((ℝ × ℝ) × ℝ) →ᴬ[ℝ] ((ℝ × ℝ) × ℝ) :=
  ((ContinuousAffineMap.id ℝ ℝ).prodMap
    (((b - a) / (2 * r)) • ContinuousAffineMap.id ℝ ℝ +
      ContinuousAffineMap.const ℝ ℝ ((a + b) / 2))).prodMap
        (ContinuousAffineMap.id ℝ ℝ)

theorem longitudinalPrismCoordinates_apply (r a b : ℝ) (x : (ℝ × ℝ) × ℝ) :
    longitudinalPrismCoordinates r a b x =
      ((x.1.1, (b - a) / (2 * r) * x.1.2 + (a + b) / 2), x.2) := rfl

theorem longitudinalPrismCoordinates_properties {r a b : ℝ}
    (hr : 0 < r) (hab : a < b) :
    Function.Injective (longitudinalPrismCoordinates r a b) ∧
      longitudinalPrismCoordinates r a b '' box r =
        (Icc (-r) r ×ˢ Icc a b) ×ˢ Icc (-r) r ∧
      (∀ t z, longitudinalPrismCoordinates r a b ((t, -r), z) = ((t, a), z)) ∧
      ∀ t z, longitudinalPrismCoordinates r a b ((t, r), z) = ((t, b), z) := by
  let k : ℝ := (b - a) / (2 * r)
  let m : ℝ := (a + b) / 2
  have hk : 0 < k := div_pos (sub_pos.mpr hab) (mul_pos (by norm_num) hr)
  have hleft : k * (-r) + m = a := by
    dsimp [k, m]
    field_simp [hr.ne']
    <;> ring
  have hright : k * r + m = b := by
    dsimp [k, m]
    field_simp [hr.ne']
    <;> ring
  have hmem (s : ℝ) : s ∈ Icc (-r) r ↔ k * s + m ∈ Icc a b := by
    constructor
    · intro hs
      constructor
      · have h := mul_le_mul_of_nonneg_left hs.1 hk.le
        linarith
      · have h := mul_le_mul_of_nonneg_left hs.2 hk.le
        linarith
    · intro hs
      constructor
      · apply (mul_le_mul_iff_right₀ hk).mp
        linarith [hs.1]
      · apply (mul_le_mul_iff_right₀ hk).mp
        linarith [hs.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have ht : x.1.1 = y.1.1 := by
      simpa only [longitudinalPrismCoordinates_apply] using
        congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.1) hxy
    have hz : x.2 = y.2 := by
      simpa only [longitudinalPrismCoordinates_apply] using
        congrArg (fun z : (ℝ × ℝ) × ℝ => z.2) hxy
    have hs : k * x.1.2 + m = k * y.1.2 + m :=
      congrArg (fun z : (ℝ × ℝ) × ℝ => z.1.2) hxy
    exact Prod.ext (Prod.ext ht (mul_left_cancel₀ hk.ne' (add_right_cancel hs))) hz
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨hx.1.1, (hmem x.1.2).mp hx.1.2⟩, hx.2⟩
    · intro hy
      let s : ℝ := (y.1.2 - m) / k
      have hsvalue : k * s + m = y.1.2 := by
        dsimp [s]
        rw [mul_div_cancel₀ _ hk.ne']
        ring
      have hs : s ∈ Icc (-r) r := (hmem s).mpr (hsvalue.symm ▸ hy.1.2)
      refine ⟨((y.1.1, s), y.2), ⟨⟨hy.1.1, hs⟩, hy.2⟩, ?_⟩
      exact Prod.ext (Prod.ext rfl hsvalue) rfl
  · intro t z
    exact Prod.ext (Prod.ext rfl hleft) rfl
  · intro t z
    exact Prod.ext (Prod.ext rfl hright) rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem reparametrize_longitudinal_prism {r a b : ℝ}
    (hr : 0 < r) (hab : a < b) {g : ((ℝ × ℝ) × ℝ) → E}
    (hg : FinitePiecewiseAffineOn g ((Icc (-r) r ×ˢ Icc a b) ×ˢ Icc (-r) r))
    (hinj : InjOn g ((Icc (-r) r ×ˢ Icc a b) ×ˢ Icc (-r) r)) :
    FinitePiecewiseAffineOn (g ∘ longitudinalPrismCoordinates r a b) (box r) ∧
      InjOn (g ∘ longitudinalPrismCoordinates r a b) (box r) ∧
      (g ∘ longitudinalPrismCoordinates r a b) '' box r =
        g '' ((Icc (-r) r ×ˢ Icc a b) ×ˢ Icc (-r) r) ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
        ((g ∘ longitudinalPrismCoordinates r a b) '' box r)
        ((g ∘ longitudinalPrismCoordinates r a b) '' boxBoundary r) := by
  obtain ⟨hNinj, hNimage, _, _⟩ := longitudinalPrismCoordinates_properties hr hab
  have hmap : MapsTo (longitudinalPrismCoordinates r a b) (box r)
      ((Icc (-r) r ×ˢ Icc a b) ×ˢ Icc (-r) r) := by
    intro x hx
    exact hNimage.subset (mem_image_of_mem _ hx)
  have hcopy := box_ballPair hr
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hN : FinitePiecewiseAffineOn (longitudinalPrismCoordinates r a b) (box r) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine (longitudinalPrismCoordinates r a b)⟩
  have hcomp := hg.comp hN hmap
  have hcompInj : InjOn (g ∘ longitudinalPrismCoordinates r a b) (box r) := by
    intro x hx y hy hxy
    exact hNinj (hinj (hmap hx) (hmap hy) hxy)
  refine ⟨hcomp, hcompInj, ?_, (box_ballPair hr).image hcomp hcompInj⟩
  calc
    (g ∘ longitudinalPrismCoordinates r a b) '' box r =
        g '' (longitudinalPrismCoordinates r a b '' box r) :=
      (image_image g (longitudinalPrismCoordinates r a b) (box r)).symm
    _ = _ := congrArg (g '' ·) hNimage

end CoordinateHalfBoxes
