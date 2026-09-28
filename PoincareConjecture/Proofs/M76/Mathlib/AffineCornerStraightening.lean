import PoincareConjecture.Proofs.M76.Mathlib.PLBandCutoff

set_option autoImplicit false

open Set Geometry

namespace ContinuousAffineMap

theorem exists_corner_straightening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a b : E →ᴬ[ℝ] ℝ) (v w : E)
    (hav : a.contLinear v = 1) (hbv : b.contLinear v = 0)
    (haw : a.contLinear w = 0) (hbw : b.contLinear w = 1) :
    ∃ H : E ≃ₜ E, H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      (∀ y, a (H y) = min (a y) (b y)) ∧
      (∀ y, b (H y) = b y - a y) ∧
      (∀ y, a y = 0 → b y = 0 → H y = y) ∧
      (∀ y, (0 ≤ a y ∧ 0 ≤ b y) ↔ 0 ≤ a (H y)) ∧
      (∀ y, (a y = 0 ∧ 0 ≤ b y) ↔ (a (H y) = 0 ∧ 0 ≤ b (H y))) ∧
      ∀ y, (b y = 0 ∧ 0 ≤ a y) ↔ (a (H y) = 0 ∧ b (H y) ≤ 0) := by
  let q : E → ℝ := fun y => max 0 (a y - b y)
  let r : E → ℝ := fun y => max 0 (-b y)
  let F : E → E := fun y => (-q y) • v + ((-a y) • w + y)
  let G : E → E := fun y => r y • v + ((a y + r y) • w + y)
  have haF (y : E) : a (F y) = a y - q y := by
    change a ((-q y) • v +ᵥ ((-a y) • w +ᵥ y)) = _
    rw [map_vadd, map_vadd, map_smul, map_smul, hav, haw]
    change (-q y) * 1 + ((-a y) * 0 + a y) = a y - q y
    ring
  have hbF (y : E) : b (F y) = b y - a y := by
    change b ((-q y) • v +ᵥ ((-a y) • w +ᵥ y)) = _
    rw [map_vadd, map_vadd, map_smul, map_smul, hbv, hbw]
    change (-q y) * 0 + ((-a y) * 1 + b y) = b y - a y
    ring
  have haG (y : E) : a (G y) = a y + r y := by
    change a (r y • v +ᵥ ((a y + r y) • w +ᵥ y)) = _
    rw [map_vadd, map_vadd, map_smul, map_smul, hav, haw]
    change r y * 1 + ((a y + r y) * 0 + a y) = a y + r y
    ring
  have hbG (y : E) : b (G y) = b y + a y + r y := by
    change b (r y • v +ᵥ ((a y + r y) • w +ᵥ y)) = _
    rw [map_vadd, map_vadd, map_smul, map_smul, hbv, hbw]
    change r y * 0 + ((a y + r y) * 1 + b y) = b y + a y + r y
    ring
  have hrF (y : E) : r (F y) = q y := by
    change max 0 (-b (F y)) = max 0 (a y - b y)
    rw [hbF]
    congr 1
    ring
  have hqG (y : E) : q (G y) = r y := by
    change max 0 (a (G y) - b (G y)) = max 0 (-b y)
    rw [haG, hbG]
    congr 1
    ring
  have hleft : Function.LeftInverse G F := by
    intro y
    change r (F y) • v + ((a (F y) + r (F y)) • w + F y) = y
    rw [hrF, haF, sub_add_cancel]
    dsimp only [F]
    simp only [neg_smul]
    abel
  have hright : Function.RightInverse G F := by
    intro y
    change (-q (G y)) • v + ((-a (G y)) • w + G y) = y
    rw [hqG, haG]
    dsimp only [G]
    simp only [neg_smul]
    abel
  have hqc : Continuous q := continuous_const.max (a.continuous.sub b.continuous)
  have hrc : Continuous r := continuous_const.max b.continuous.neg
  let H : E ≃ₜ E :=
    { toFun := F
      invFun := G
      left_inv := hleft
      right_inv := hright
      continuous_toFun := (hqc.neg.smul continuous_const).add
        ((a.continuous.neg.smul continuous_const).add continuous_id)
      continuous_invFun := (hrc.smul continuous_const).add
        (((a.continuous.add hrc).smul continuous_const).add continuous_id) }
  let V := ((ContinuousLinearMap.id ℝ ℝ).smulRight v).toContinuousAffineMap
  let W := ((ContinuousLinearMap.id ℝ ℝ).smulRight w).toContinuousAffineMap
  have hqPL : LocallyPiecewiseAffineOn q univ :=
    (locallyPiecewiseAffineOn_affine (0 : E →ᴬ[ℝ] ℝ) isOpen_univ).max
      (locallyPiecewiseAffineOn_affine (a - b) isOpen_univ)
  have hrPL : LocallyPiecewiseAffineOn r univ :=
    (locallyPiecewiseAffineOn_affine (0 : E →ᴬ[ℝ] ℝ) isOpen_univ).max
      (locallyPiecewiseAffineOn_affine (-b) isOpen_univ)
  have hFPL : LocallyPiecewiseAffineOn F univ := by
    intro x hx
    obtain ⟨K, hK, hxK, hKU, hqK⟩ := hqPL x hx
    refine ⟨K, hK, hxK, hKU, ?_⟩
    intro s hs
    obtain ⟨d, hd⟩ := hqK s hs
    refine ⟨-(V.comp d) + (-(W.comp a) + ContinuousAffineMap.id ℝ E), ?_⟩
    intro y hy
    change (-q y) • v + ((-a y) • w + y) = -(d y • v) + (-(a y • w) + y)
    rw [hd hy, neg_smul, neg_smul]
  have hGPL : LocallyPiecewiseAffineOn G univ := by
    intro x hx
    obtain ⟨K, hK, hxK, hKU, hrK⟩ := hrPL x hx
    refine ⟨K, hK, hxK, hKU, ?_⟩
    intro s hs
    obtain ⟨d, hd⟩ := hrK s hs
    refine ⟨V.comp d + (W.comp (a + d) + ContinuousAffineMap.id ℝ E), ?_⟩
    intro y hy
    change r y • v + ((a y + r y) • w + y) = d y • v + ((a y + d y) • w + y)
    rw [hd hy]
  have hmin (y : E) : a (H y) = min (a y) (b y) := by
    change a (F y) = _
    rw [haF]
    dsimp only [q]
    by_cases hab : a y ≤ b y
    · rw [max_eq_left (sub_nonpos.mpr hab), min_eq_left hab, sub_zero]
    · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge hab)),
        min_eq_right (le_of_not_ge hab)]
      ring
  have hbH (y : E) : b (H y) = b y - a y := hbF y
  refine ⟨H, ⟨hFPL, hGPL⟩, hmin, hbH, ?_, ?_, ?_, ?_⟩
  · intro y hay hby
    change F y = y
    simp only [F, q, hay, hby, sub_self, max_self, neg_zero, zero_smul, zero_add]
  · intro y
    rw [hmin]
    exact le_min_iff.symm
  · intro y
    rw [hmin, hbH]
    constructor
    · rintro ⟨hay, hby⟩
      rw [hay, min_eq_left hby, sub_zero]
      exact ⟨rfl, hby⟩
    · rintro ⟨hzero, hdiff⟩
      have hab : a y ≤ b y := sub_nonneg.mp hdiff
      rw [min_eq_left hab] at hzero
      exact ⟨hzero, by linarith⟩
  · intro y
    rw [hmin, hbH]
    constructor
    · rintro ⟨hby, hay⟩
      rw [hby, min_eq_right hay, zero_sub]
      exact ⟨rfl, neg_nonpos.mpr hay⟩
    · rintro ⟨hzero, hdiff⟩
      have hba : b y ≤ a y := sub_nonpos.mp hdiff
      rw [min_eq_right hba] at hzero
      exact ⟨hzero, by linarith⟩

end ContinuousAffineMap
