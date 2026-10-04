import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.ComplexConnection
import PoincareLib.Geometry.Riemannian.LoopSpace.Width
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# The actual covector frame for boundary reflection

The metric tangent row and two transverse rows form an invertible
frame without dividing by the disk differential. The actual reflected
complex coordinates use signed conjugation. Source: M65 derivation 43,
actual target frame, for Heinz 1970, pp. 99--105, and MT 19.2,
pp. 438--439.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Complex
open scoped ContDiff

namespace PoincareMT.M65StrictTrace

open M65Branch

/-- The genuine metric tangent covector and transverse covectors.
Source: derivation 43, actual target frame. -/
def rowFrame (G : LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (V : LoopAmbient) (j : Fin 3) : LoopAmbient →L[ℝ] LoopAmbient :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k => if k = j then G V else
      EuclideanSpace.proj k - (V k / V j) • EuclideanSpace.proj j)

/-- Every row has its literal geometric value. Source:
derivation 43, actual target frame. -/
theorem rowFrame_apply (G : LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (V W : LoopAmbient) (j k : Fin 3) :
    rowFrame G V j W k = if k = j then G V W else W k - (V k / V j) * W j := by
  simp only [rowFrame, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    EuclideanSpace.equiv, PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_apply,
    ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

/-- Actual metric positivity makes the covector frame invertible at
every nonzero chosen tangent component. Source: derivation 43,
actual target frame; no disk differential is divided by. -/
theorem rowFrame_injective (G : LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (V : LoopAmbient) (j : Fin 3) (hV : V j ≠ 0)
    (hpos : ∀ W : LoopAmbient, W ≠ 0 → 0 < G W W) :
    Function.Injective (rowFrame G V j) := by
  have hzero (W : LoopAmbient) (hW : rowFrame G V j W = 0) : W = 0 := by
    have hrows (k : Fin 3) : (if k = j then G V W else W k - (V k / V j) * W j) = 0 := by
      rw [← rowFrame_apply]
      exact congrArg (fun X : LoopAmbient => X k) hW
    have hform : W = (W j / V j) • V := by
      ext k
      change W k = (W j / V j) * V k
      by_cases hk : k = j
      · subst k
        exact (div_mul_cancel₀ (W j) hV).symm
      · have h := hrows k
        rw [if_neg hk] at h
        linear_combination h
    have hV0 : V ≠ 0 := fun h => hV (by rw [h]; rfl)
    have hG : G V W = 0 := by simpa using hrows j
    rw [hform, map_smul, smul_eq_mul] at hG
    have ha : W j / V j = 0 := (mul_eq_zero.mp hG).resolve_right (hpos V hV0).ne'
    rw [hform, ha, zero_smul]
  intro W Z heq
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, heq, sub_self]

/-- The genuine rows vary smoothly whenever the actual metric and
chosen nonvanishing tangent field do. Source: derivation 43,
actual target frame. -/
theorem contDiffOn_rowFrame
    {G : LoopAmbient → LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ}
    {V : LoopAmbient → LoopAmbient} {U : Set LoopAmbient} (j : Fin 3)
    (hG : ContDiffOn ℝ ∞ G U) (hV : ContDiffOn ℝ ∞ V U)
    (hj : ∀ q ∈ U, V q j ≠ 0) :
    ContDiffOn ℝ ∞ (fun q => rowFrame (G q) (V q) j) U := by
  apply contDiffOn_clm_apply.mpr
  intro W
  have hv (k : Fin 3) : ContDiffOn ℝ ∞ (fun q => V q k) U :=
    (EuclideanSpace.proj k : LoopAmbient →L[ℝ] ℝ).contDiff.comp_contDiffOn hV
  have hrows : ContDiffOn ℝ ∞
      (fun q => fun k : Fin 3 => if k = j then G q (V q) W else
        W k - (V q k / V q j) * W j) U := by
    apply contDiffOn_pi.mpr
    intro k
    by_cases hk : k = j
    · simpa only [if_pos hk] using (hG.clm_apply hV).clm_apply contDiffOn_const
    · convert! (contDiffOn_const (c := W k)).sub
        (((hv k).div (hv j) hj).mul (contDiffOn_const (c := W j))) using 1
      funext q
      simp only [if_neg hk]
      rfl
  have h := (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp_contDiffOn hrows
  apply h.congr
  intro q _
  ext k
  exact rowFrame_apply (G q) (V q) W j k

/-- The actual signed conjugation required by the boundary rows.
Source: derivation 43, actual reflection. -/
def boundaryReflection (j : Fin 3) : (Fin 3 → ℂ) ≃ₗᵢ[ℝ] (Fin 3 → ℂ) := by
  let e (k : Fin 3) : ℂ ≃ₗᵢ[ℝ] ℂ :=
    if k = j then conjLIE else conjLIE.trans (LinearIsometryEquiv.neg ℝ)
  exact {
    toLinearEquiv := LinearEquiv.piCongrRight fun k => (e k).toLinearEquiv
    norm_map' := fun v => by
      simp only [Pi.norm_def, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.nnnorm_map] }

/-- The reflection is exactly conjugation in the tangent row and
negative conjugation in the transverse rows. Source: derivation 43. -/
theorem boundaryReflection_apply (j : Fin 3) (v : Fin 3 → ℂ) (k : Fin 3) :
    boundaryReflection j v k = if k = j then star (v k) else -star (v k) := by
  simp only [boundaryReflection, LinearIsometryEquiv.coe_mk,
    LinearEquiv.piCongrRight_apply]
  split_ifs <;> rfl

/-- The actual reflection is anti-complex, as required by the shared
half-disk theorem. Source: derivation 43, actual reflection. -/
theorem boundaryReflection_smul (j : Fin 3) (c : ℂ) (v : Fin 3 → ℂ) :
    boundaryReflection j (c • v) = star c • boundaryReflection j v := by
  ext k
  simp only [boundaryReflection_apply, Pi.smul_apply, smul_eq_mul, star_mul]
  split_ifs <;> ring

/-- The actual reflection is an involution, including all zero
coordinates. Source: derivation 43, actual reflection. -/
theorem boundaryReflection_involutive (j : Fin 3) :
    Function.Involutive (boundaryReflection j) := by
  intro v
  ext k
  simp only [boundaryReflection_apply]
  split_ifs <;> simp

/-- The actual tangent and normal columns have the required frame
components, even when the tangential column is zero. Source:
derivation 43, conformality at the actual boundary. -/
theorem rowFrame_boundary_columns
    (G : LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (V X Y : LoopAmbient) (j : Fin 3) (hV : V j ≠ 0)
    (hpos : ∀ W : LoopAmbient, W ≠ 0 → 0 < G W W)
    (hX : ∃ a : ℝ, X = a • V)
    (hdiag : G X X = G Y Y) (hmixed : G X Y = 0) :
    rowFrame G V j Y j = 0 ∧ ∀ k, k ≠ j → rowFrame G V j X k = 0 := by
  obtain ⟨a, rfl⟩ := hX
  constructor
  · rw [rowFrame_apply, if_pos rfl]
    by_cases ha : a = 0
    · have hYY : G Y Y = 0 := by simpa only [ha, zero_smul, map_zero, zero_apply] using hdiag.symm
      have hY : Y = 0 := by
        by_contra hn
        exact (hpos Y hn).ne' hYY
      rw [hY, map_zero]
    · have hh : a * G V Y = 0 := by
        simpa only [map_smul, smul_apply, smul_eq_mul] using hmixed
      exact (mul_eq_zero.mp hh).resolve_left ha
  · intro k hk
    rw [rowFrame_apply, if_neg hk]
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- The genuine signed reflection fixes exactly the complex boundary
columns just obtained. Source: derivation 43, actual diameter reality. -/
theorem boundaryReflection_of_rows (j : Fin 3) (X Y : LoopAmbient)
    (hY : Y j = 0) (hX : ∀ k, k ≠ j → X k = 0) :
    boundaryReflection j (coordinateComplexification X - I • coordinateComplexification Y) =
      coordinateComplexification X - I • coordinateComplexification Y := by
  ext k
  rw [boundaryReflection_apply]
  change (if k = j then star ((X k : ℂ) - I * (Y k : ℂ)) else
    -star ((X k : ℂ) - I * (Y k : ℂ))) = (X k : ℂ) - I * (Y k : ℂ)
  by_cases hk : k = j
  · subst k
    simp [hY]
  · simp [hk, hX k hk]

/-- The actual complexified frame supplies the literal reflection
identity, with no boundary immersion premise. Source: derivation 43,
actual target frame and diameter reality. -/
theorem rowFrame_boundary_reflection
    (G : LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (V X Y : LoopAmbient) (j : Fin 3) (hV : V j ≠ 0)
    (hpos : ∀ W : LoopAmbient, W ≠ 0 → 0 < G W W)
    (hX : ∃ a : ℝ, X = a • V)
    (hdiag : G X X = G Y Y) (hmixed : G X Y = 0) :
    boundaryReflection j (complexifyOperator (rowFrame G V j)
      (coordinateComplexification X - I • coordinateComplexification Y)) =
      complexifyOperator (rowFrame G V j)
        (coordinateComplexification X - I • coordinateComplexification Y) := by
  obtain ⟨hY, hX⟩ := rowFrame_boundary_columns G V X Y j hV hpos hX hdiag hmixed
  simpa only [map_sub, map_smul, complexifyOperator_real] using
    boundaryReflection_of_rows j (rowFrame G V j X) (rowFrame G V j Y) hY hX

/-- Complexification preserves actual injectivity. Source:
derivation 43, invertibility of the actual target frame. -/
theorem complexifyOperator_injective {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hL : Function.Injective L) : Function.Injective (complexifyOperator L) := by
  have hzero (v : Fin n → ℂ) (hv : complexifyOperator L v = 0) : v = 0 := by
    let a : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun k => (v k).re)
    let b : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun k => (v k).im)
    have hvab : v = coordinateComplexification a + I • coordinateComplexification b := by
      ext k
      change v k = ((v k).re : ℂ) + I * ((v k).im : ℂ)
      simpa only [mul_comm] using (Complex.re_add_im (v k)).symm
    have heq : coordinateComplexification (L a) + I • coordinateComplexification (L b) = 0 := by
      rw [hvab, map_add, map_smul, complexifyOperator_real, complexifyOperator_real] at hv
      exact hv
    have ha : L a = 0 := by
      ext k
      have hk := congrArg (fun w : Fin n → ℂ => (w k).re) heq
      change (((L a) k : ℂ) + I * ((L b) k : ℂ)).re = 0 at hk
      simpa using hk
    have hb : L b = 0 := by
      ext k
      have hk := congrArg (fun w : Fin n → ℂ => (w k).im) heq
      change (((L a) k : ℂ) + I * ((L b) k : ℂ)).im = 0 at hk
      simpa using hk
    have ha0 : a = 0 := hL (ha.trans L.map_zero.symm)
    have hb0 : b = 0 := hL (hb.trans L.map_zero.symm)
    rw [hvab, ha0, hb0, map_zero, smul_zero, add_zero]
  intro v w hvw
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hvw, sub_self]

/-- The genuine boundary frame is a unit in the complex operator
algebra used by Hartman--Wintner. Source: derivation 43, actual frame. -/
theorem rowFrame_complex_isUnit
    (G : LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (V : LoopAmbient) (j : Fin 3) (hV : V j ≠ 0)
    (hpos : ∀ W : LoopAmbient, W ≠ 0 → 0 < G W W) :
    IsUnit (complexifyOperator (rowFrame G V j)) := by
  have hi := complexifyOperator_injective (rowFrame G V j)
    (rowFrame_injective G V j hV hpos)
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, (LinearMap.injective_iff_surjective).mp hi⟩

end PoincareMT.M65StrictTrace
