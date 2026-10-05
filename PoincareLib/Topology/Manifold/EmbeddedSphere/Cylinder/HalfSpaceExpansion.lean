import PoincareLib.Topology.Metric.Complements.CompactConvexComplement

/-!
# Radial expansion clipped at the horizontal plane

Outward expansion from an off-plane puncture can be stopped at the plane.
It then preserves the corresponding closed half-space, fixes the plane,
and ends on the plane or beyond a prescribed radius. Convex exteriors
are preserved throughout. This is the explicit local construction in M53
derivation 07 for the separation repair of Morgan--Tian, Proposition 15.12
and Remark 15.13, p. 365; pair homotopy invariance is Hatcher, p. 118.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped unitInterval
open Poincare.Topology

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {E : Type u} [NormedAddCommGroup E]

private def clippedScale (d b : ℝ) : ℝ := max 1 (max d b)⁻¹

private theorem clippedScale_ge_one (d b : ℝ) : 1 ≤ clippedScale d b :=
  le_max_left _ _

private theorem clippedScale_mul_le_one {d b : ℝ} (hd : 0 < d) (hb : b ≤ 1) :
    clippedScale d b * b ≤ 1 := by
  by_cases hb0 : 0 ≤ b
  · rw [clippedScale, max_mul_of_nonneg _ _ hb0, one_mul]
    exact max_le hb ((inv_mul_le_one₀ (hd.trans_le (le_max_left _ _))).mpr
      (le_max_right _ _))
  · have ha := (zero_lt_one.trans_le (clippedScale_ge_one d b)).le
    exact (mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hb0)).trans zero_le_one

private theorem clippedScale_endpoint {d b : ℝ} (hd : 0 < d) (hb : b ≤ 1) :
    1 ≤ clippedScale d b * d ∨ clippedScale d b * b = 1 := by
  by_cases hdb : b ≤ d
  · left
    have h := mul_le_mul_of_nonneg_right
      (le_max_right 1 (max d b)⁻¹) hd.le
    rw [max_eq_left hdb, inv_mul_cancel₀ hd.ne'] at h
    simpa only [clippedScale, max_eq_left hdb] using h
  · right
    have hbd : d < b := lt_of_not_ge hdb
    have hb0 := hd.trans hbd
    rw [clippedScale, max_eq_right hbd.le,
      max_eq_right ((one_le_inv₀ hb0).mpr hb), inv_mul_cancel₀ hb0.ne']

private theorem clippedScale_one (d : ℝ) : clippedScale d 1 = 1 := by
  rw [clippedScale, max_eq_left]
  exact (inv_le_one₀ (zero_lt_one.trans_le (le_max_right _ _))).mpr (le_max_right _ _)

/-- The scale for outward expansion from `(0,c)`, clipped at height zero.
It is continuous on the puncture for every positive radius. Source: M53
derivation 07, for Morgan--Tian, p. 365. -/
def halfSpaceExpansionScale (c R : ℝ) (hR : 0 < R) :
    C(({((0 : E), c)}ᶜ : Set (E × ℝ)), ℝ) := by
  let q : E × ℝ := (0, c)
  have hd (y : ({q}ᶜ : Set (E × ℝ))) : 0 < ‖y.val - q‖ / R :=
    div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr y.property)) hR
  refine ⟨fun y => clippedScale (‖y.val - q‖ / R) (1 - y.val.2 / c), ?_⟩
  unfold clippedScale
  apply continuous_const.max
  apply Continuous.inv₀
  · exact ((continuous_subtype_val.sub continuous_const).norm.div_const R).max
      (continuous_const.sub ((continuous_snd.comp continuous_subtype_val).div_const c))
  · intro y
    exact (hd y |>.trans_le (le_max_left _ _)).ne'

/-- Every clipped expansion is outward. Source: M53 derivation 07,
for Morgan--Tian, p. 365. -/
theorem halfSpaceExpansionScale_ge_one (c R : ℝ) (hR : 0 < R)
    (y : ({((0 : E), c)}ᶜ : Set (E × ℝ))) :
    1 ≤ halfSpaceExpansionScale c R hR y := clippedScale_ge_one _ _

variable [NormedSpace ℝ E]

/-- The interpolation from the clipped expansion to the identity, as an
ambient continuous map. Source: M53 derivation 07 and Hatcher, p. 118. -/
def halfSpaceExpansion (c R : ℝ) (hR : 0 < R) :
    C(unitInterval × ({((0 : E), c)}ᶜ : Set (E × ℝ)), E × ℝ) :=
  ⟨fun p => (0, c) +
      AffineMap.lineMap (halfSpaceExpansionScale c R hR p.2) 1 (p.1 : ℝ) •
        (p.2.val - (0, c)), by
    have ha : Continuous (fun p : unitInterval × ({((0 : E), c)}ᶜ : Set (E × ℝ)) =>
        AffineMap.lineMap (halfSpaceExpansionScale c R hR p.2) 1 (p.1 : ℝ)) := by
      simp only [AffineMap.lineMap_apply_ring]
      fun_prop
    exact continuous_const.add
      (ha.smul ((continuous_subtype_val.comp continuous_snd).sub continuous_const))⟩

omit [NormedSpace ℝ E] in
private theorem halfSpaceExpansion_scale_bounds (c R : ℝ) (hR : 0 < R)
    (s : unitInterval) (y : ({((0 : E), c)}ᶜ : Set (E × ℝ))) :
    AffineMap.lineMap (halfSpaceExpansionScale c R hR y) 1 (s : ℝ) ∈
      Icc 1 (halfSpaceExpansionScale c R hR y) := by
  exact (convex_Icc _ _).lineMap_mem
    ⟨halfSpaceExpansionScale_ge_one c R hR y, le_rfl⟩
    ⟨le_rfl, halfSpaceExpansionScale_ge_one c R hR y⟩ s.property

/-- The expansion never reaches its own puncture. Source: M53 derivation
07, for Morgan--Tian, p. 365. -/
theorem halfSpaceExpansion_ne_center (c R : ℝ) (hR : 0 < R)
    (s : unitInterval) (y : ({((0 : E), c)}ᶜ : Set (E × ℝ))) :
    halfSpaceExpansion c R hR (s, y) ≠ (0, c) := by
  have ha := zero_lt_one.trans_le (halfSpaceExpansion_scale_bounds c R hR s y).1
  intro h
  have hzero : AffineMap.lineMap (halfSpaceExpansionScale c R hR y) 1 (s : ℝ) •
      (y.val - ((0 : E), c)) = 0 := by
    exact add_left_cancel (h.trans (add_zero ((0 : E), c)).symm)
  exact (sub_ne_zero.mpr y.property) ((smul_eq_zero.mp hzero).resolve_left ha.ne')

/-- The final time of the interpolation is the identity. Source: M53
derivation 07 and Hatcher, p. 118. -/
theorem halfSpaceExpansion_one (c R : ℝ) (hR : 0 < R)
    (y : ({((0 : E), c)}ᶜ : Set (E × ℝ))) :
    halfSpaceExpansion c R hR (1, y) = y.val := by
  change (0, c) + AffineMap.lineMap (halfSpaceExpansionScale c R hR y) 1 (1 : ℝ) •
    (y.val - (0, c)) = y.val
  rw [AffineMap.lineMap_apply_one, one_smul, add_sub_cancel]

/-- The whole interpolation fixes the horizontal plane, allowing its two
halves to be pasted continuously. Source: M53 derivation 07, p. 365 repair. -/
theorem halfSpaceExpansion_plane (c R : ℝ) (hR : 0 < R)
    (s : unitInterval) (y : ({((0 : E), c)}ᶜ : Set (E × ℝ))) (hy : y.val.2 = 0) :
    halfSpaceExpansion c R hR (s, y) = y.val := by
  have hs : halfSpaceExpansionScale c R hR y = 1 := by
    change clippedScale _ (1 - y.val.2 / c) = 1
    rw [hy, zero_div, sub_zero, clippedScale_one]
  change (0, c) + AffineMap.lineMap (halfSpaceExpansionScale c R hR y) 1 (s : ℝ) •
    (y.val - (0, c)) = y.val
  rw [hs, AffineMap.lineMap_same, AffineMap.const_apply, one_smul, add_sub_cancel]

/-- The interpolation preserves the closed half-space containing its
center, expressed by normalized height. The center height must be nonzero.
Source: M53 derivation 07, for Morgan--Tian, p. 365. -/
theorem halfSpaceExpansion_height (c R : ℝ) (hc : c ≠ 0) (hR : 0 < R)
    (s : unitInterval) (y : ({((0 : E), c)}ᶜ : Set (E × ℝ)))
    (hy : 0 ≤ y.val.2 / c) : 0 ≤ (halfSpaceExpansion c R hR (s, y)).2 / c := by
  let a := AffineMap.lineMap (halfSpaceExpansionScale c R hR y) 1 (s : ℝ)
  let b := 1 - y.val.2 / c
  have hd : 0 < ‖y.val - ((0 : E), c)‖ / R :=
    div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr y.property)) hR
  have hbound : a * b ≤ 1 := by
    by_cases hb : 0 ≤ b
    · exact (mul_le_mul_of_nonneg_right
        (halfSpaceExpansion_scale_bounds c R hR s y).2 hb).trans
          (clippedScale_mul_le_one hd (by linarith))
    · exact (mul_nonpos_of_nonneg_of_nonpos
        (zero_le_one.trans (halfSpaceExpansion_scale_bounds c R hR s y).1)
        (le_of_not_ge hb)).trans zero_le_one
  have he : (halfSpaceExpansion c R hR (s, y)).2 / c = 1 - a * b := by
    change (c + a * (y.val.2 - c)) / c = 1 - a * b
    dsimp [b]
    field_simp [hc]
    ring
  rw [he]
  linarith

/-- At the initial time the image lies on the plane or at distance at
least the chosen radius from its center. Source: M53 derivation 07. -/
theorem halfSpaceExpansion_zero_mem (c R : ℝ) (hc : c ≠ 0) (hR : 0 < R)
    (y : ({((0 : E), c)}ᶜ : Set (E × ℝ))) (hy : 0 ≤ y.val.2 / c) :
    (halfSpaceExpansion c R hR (0, y)).2 = 0 ∨
      R ≤ ‖halfSpaceExpansion c R hR (0, y) - (0, c)‖ := by
  let a := halfSpaceExpansionScale c R hR y
  have hd : 0 < ‖y.val - ((0 : E), c)‖ / R :=
    div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr y.property)) hR
  rcases clippedScale_endpoint hd (show 1 - y.val.2 / c ≤ 1 by linarith) with hn | hz
  · right
    change R ≤ ‖((0 : E), c) + AffineMap.lineMap a 1 (0 : ℝ) •
      (y.val - (0, c)) - (0, c)‖
    rw [AffineMap.lineMap_apply_zero, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (zero_le_one.trans (halfSpaceExpansionScale_ge_one c R hR y))]
    change 1 ≤ a * (‖y.val - ((0 : E), c)‖ / R) at hn
    rw [← mul_div_assoc] at hn
    simpa only [one_mul] using (le_div_iff₀ hR).mp hn
  · left
    change c + AffineMap.lineMap a 1 (0 : ℝ) * (y.val.2 - c) = 0
    rw [AffineMap.lineMap_apply_zero]
    have hz' : a * (1 - y.val.2 / c) = 1 := hz
    field_simp [hc] at hz'
    nlinarith

/-- Convex exteriors are preserved at every time by the outward motion.
Source: M02 convex-complement comparison and M53 derivation 07. -/
theorem halfSpaceExpansion_not_mem (c R : ℝ) (hR : 0 < R)
    (K : Set (E × ℝ)) (hK : Convex ℝ K) (hq : ((0 : E), c) ∈ K)
    (s : unitInterval) (y : ({((0 : E), c)}ᶜ : Set (E × ℝ))) (hy : y.val ∉ K) :
    halfSpaceExpansion c R hR (s, y) ∉ K :=
  convex_complement_outward K hK (0, c) hq y.val hy _
    (halfSpaceExpansion_scale_bounds c R hR s y).1

end PoincareMT.Topology.EmbeddedSphere
