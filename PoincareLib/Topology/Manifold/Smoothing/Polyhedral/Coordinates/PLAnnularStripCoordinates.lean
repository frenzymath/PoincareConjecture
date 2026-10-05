import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLArithmetic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Exact finite PL coordinates for an annular strip

Positive parts give a rectangle-to-trapezoid coordinate whose
middle region is the identity and whose ends are the two miter
lines. Strict monotonicity identifies its exact range. This
constructs a band used in Hatcher's punctured-torus picture,
p. 7, for Hamilton 1976, p. 66. See M76 derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip

/-- The finite PL correction at one strip end. Its support
stays within twice the transverse distance from that end.
See Hatcher p. 7 and M76 derivation 270. -/
noncomputable def cornerCorrection (s t : ℝ) : ℝ :=
  max 0 (t - s / 2) - max 0 (-t - s / 2)

/-- The actual longitudinal coordinate, with opposite end
corrections and an exactly fixed middle interval. See
Hatcher p. 7 and M76 derivation 270. -/
noncomputable def coordinate (L s t : ℝ) : ℝ :=
  s + cornerCorrection s t - cornerCorrection (L - s) t

/-- The actual planar strip map retains the transverse
coordinate. See Hatcher p. 7 and M76 derivation 270. -/
noncomputable def stripMap (L : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (coordinate L p.1 p.2, p.2)

/-- The end correction is continuous through its two break
lines. See M76 derivation 270. -/
theorem continuous_cornerCorrection :
    Continuous (fun p : ℝ × ℝ => cornerCorrection p.1 p.2) := by
  unfold cornerCorrection
  fun_prop

/-- Both strip coordinates are jointly continuous, including
the miter edges. See M76 derivation 270. -/
theorem continuous_stripMap (L : ℝ) : Continuous (stripMap L) := by
  unfold stripMap coordinate cornerCorrection
  fun_prop

/-- At the end itself the correction is the exact transverse
coordinate. See M76 derivation 270. -/
theorem cornerCorrection_zero (t : ℝ) : cornerCorrection 0 t = t := by
  dsimp [cornerCorrection]
  rcases le_total 0 t with ht | ht
  · rw [zero_div, sub_zero, sub_zero, max_eq_right ht, max_eq_left (by linarith)]
    ring
  · rw [zero_div, sub_zero, sub_zero, max_eq_left ht, max_eq_right (by linarith)]
    ring

/-- Outside its exact corner support the correction vanishes.
See M76 derivation 270. -/
theorem cornerCorrection_eq_zero {s t : ℝ} (h : 2 * |t| ≤ s) :
    cornerCorrection s t = 0 := by
  have h₁ : t - s / 2 ≤ 0 := by linarith [le_abs_self t]
  have h₂ : -t - s / 2 ≤ 0 := by linarith [neg_le_abs t]
  simp only [cornerCorrection, max_eq_left h₁, max_eq_left h₂, sub_self]

private theorem cornerCorrection_of_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    cornerCorrection s t = max 0 (t - s / 2) := by
  rw [cornerCorrection, max_eq_left (show -t - s / 2 ≤ 0 by linarith), sub_zero]

private theorem cornerCorrection_of_nonpos {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 0) :
    cornerCorrection s t = -max 0 (-t - s / 2) := by
  rw [cornerCorrection, max_eq_left (show t - s / 2 ≤ 0 by linarith), zero_sub]

/-- The two end values are exactly the required miter lines.
The strict width bound keeps them ordered. See M76 derivation 270. -/
theorem coordinate_endpoints {L t : ℝ} (ht : 4 * |t| < L) :
    coordinate L 0 t = t ∧ coordinate L L t = L - t := by
  have hbig : cornerCorrection L t = 0 :=
    cornerCorrection_eq_zero (by linarith [abs_nonneg t])
  simp [coordinate, cornerCorrection_zero, hbig]

/-- Every transverse fiber retains its literal middle interval.
See Hatcher p. 7 and M76 derivation 270. -/
theorem coordinate_eq_self {L s t : ℝ}
    (hleft : 2 * |t| ≤ s) (hright : 2 * |t| ≤ L - s) :
    coordinate L s t = s := by
  rw [coordinate, cornerCorrection_eq_zero hleft, cornerCorrection_eq_zero hright]
  ring

/-- A uniform lower slope bound proves that no strip fiber
folds at either break line. See M76 derivation 270. -/
theorem coordinate_lower_slope {L t a b : ℝ} (ht : 4 * |t| < L)
    (ha : a ∈ Icc 0 L) (hb : b ∈ Icc 0 L) (hab : a ≤ b) :
    b - a ≤ 2 * (coordinate L b t - coordinate L a t) := by
  rcases le_total 0 t with ht0 | ht0
  · rw [abs_of_nonneg ht0] at ht
    simp only [coordinate,
      cornerCorrection_of_nonneg ha.1 ht0,
      cornerCorrection_of_nonneg hb.1 ht0,
      cornerCorrection_of_nonneg (sub_nonneg.mpr ha.2) ht0,
      cornerCorrection_of_nonneg (sub_nonneg.mpr hb.2) ht0]
    simp only [max_def]
    split_ifs <;> linarith [ha.1, ha.2, hb.1, hb.2]
  · rw [abs_of_nonpos ht0] at ht
    simp only [coordinate,
      cornerCorrection_of_nonpos ha.1 ht0,
      cornerCorrection_of_nonpos hb.1 ht0,
      cornerCorrection_of_nonpos (sub_nonneg.mpr ha.2) ht0,
      cornerCorrection_of_nonpos (sub_nonneg.mpr hb.2) ht0]
    simp only [max_def]
    split_ifs <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- The actual longitudinal coordinate is strictly increasing
on every admissible closed strip fiber. See M76 derivation 270. -/
theorem strictMonoOn_coordinate {L t : ℝ} (ht : 4 * |t| < L) :
    StrictMonoOn (fun s => coordinate L s t) (Icc 0 L) := by
  intro a ha b hb hab
  have h := coordinate_lower_slope ht ha hb hab.le
  linarith

/-- The image of each whole longitudinal interval is exactly
the interval between its two miter endpoints. See M76 derivation 270. -/
theorem coordinate_image_Icc {L t : ℝ} (ht : 4 * |t| < L) :
    (fun s => coordinate L s t) '' Icc 0 L = Icc t (L - t) := by
  have hc : Continuous (fun s => coordinate L s t) :=
    (continuous_fst.comp (continuous_stripMap L)).comp
      (continuous_id.prodMk continuous_const)
  rw [hc.continuousOn.image_Icc_of_monotoneOn
    (show 0 ≤ L by linarith [abs_nonneg t]) (strictMonoOn_coordinate ht).monotoneOn,
    (coordinate_endpoints ht).1, (coordinate_endpoints ht).2]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The corner correction has actual finite PL formulas on
any given finite carrier, with affine source coordinates.
See Hudson pp. 12--19 and M76 derivation 270. -/
theorem finitePiecewiseAffineOn_cornerCorrection
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (s t : E →ᴬ[ℝ] ℝ) :
    FinitePiecewiseAffineOn (fun x => cornerCorrection (s x) (t x)) K.space := by
  have h₁ := (K.affineOnFaces_affine (t - (1 / 2 : ℝ) • s)).finitePiecewiseAffineOn hK
  have h₂ := (K.affineOnFaces_affine (-t - (1 / 2 : ℝ) • s)).finitePiecewiseAffineOn hK
  convert h₁.positivePart.sub h₂.positivePart using 1
  ext x
  simp [cornerCorrection, div_eq_mul_inv, mul_comm]

/-- The planar strip map is finite PL on every actual finite
carrier. Its four positive parts share one finite refinement.
See Hudson pp. 12--19 and M76 derivation 270. -/
theorem finitePiecewiseAffineOn_stripMap
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite) (L : ℝ) :
    FinitePiecewiseAffineOn (stripMap L) K.space := by
  let a : (ℝ × ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let b : (ℝ × ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  let c : (ℝ × ℝ) →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ (ℝ × ℝ) L - a
  have ha := (K.affineOnFaces_affine a).finitePiecewiseAffineOn hK
  have hb := (K.affineOnFaces_affine b).finitePiecewiseAffineOn hK
  exact ((ha.add (finitePiecewiseAffineOn_cornerCorrection K hK a b)).sub
    (finitePiecewiseAffineOn_cornerCorrection K hK c b)).prod_mk hb

end PLAnnularStrip
