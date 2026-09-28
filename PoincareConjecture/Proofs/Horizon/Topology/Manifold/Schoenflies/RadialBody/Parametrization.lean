import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Group.Bounded








noncomputable section
set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace Poincare.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]


def radialMap (r : sphere (0 : E) 1 → Real) (x : E) : E := by
  classical
  exact if hx : x = 0 then 0 else r ((homeomorphUnitSphereProd E) ⟨x, hx⟩).1 • x

@[simp] theorem radialMap_zero (r : sphere (0 : E) 1 → Real) : radialMap r 0 = 0 := by
  simp [radialMap]


theorem radialMap_smul (r : sphere (0 : E) 1 → Real)
    (p : sphere (0 : E) 1) {t : Real} (ht : 0 ≤ t) :
    radialMap r (t • (p : E)) = (r p * t) • (p : E) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hp : (p : E) ≠ 0 := ne_zero_of_mem_unit_sphere p
  have htp : t • (p : E) ≠ 0 := smul_ne_zero ht.ne' hp
  have hdir : ((homeomorphUnitSphereProd E) ⟨t • (p : E), htp⟩).1 = p := by
    apply Subtype.ext
    simp [homeomorphUnitSphereProd_apply_fst_coe, norm_smul, abs_of_pos ht,
      smul_smul, ht.ne']
  rw [radialMap, dif_neg htp, hdir, smul_smul]

@[simp] theorem radialMap_sphere (r : sphere (0 : E) 1 → Real)
    (p : sphere (0 : E) 1) : radialMap r p = r p • (p : E) := by
  simpa using radialMap_smul r p (t := 1) zero_le_one

variable [Nontrivial E]

private theorem exists_eq_norm_smul (x : E) :
    ∃ p : sphere (0 : E) 1, x = ‖x‖ • (p : E) := by
  by_cases hx : x = 0
  · obtain ⟨p, hp⟩ := NormedSpace.sphere_nonempty (E := E).mpr (show (0 : Real) ≤ 1 by norm_num)
    exact ⟨⟨p, hp⟩, by simp [hx]⟩
  · refine ⟨((homeomorphUnitSphereProd E) ⟨x, hx⟩).1, ?_⟩
    rw [homeomorphUnitSphereProd_apply_fst_coe, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

variable [ProperSpace E]


theorem continuous_radialMap {r : sphere (0 : E) 1 → Real} (hr : Continuous r) :
    Continuous (radialMap r) := by
  have hrestr : Continuous (fun x : ({0}ᶜ : Set E) => radialMap r x) := by
    convert (hr.comp (continuous_fst.comp (homeomorphUnitSphereProd E).continuous)).smul
      continuous_subtype_val using 1
    funext x
    exact dif_neg (show (x : E) ≠ 0 from x.property)
  have hon : ContinuousOn (radialMap r) ({0}ᶜ : Set E) :=
    continuousOn_iff_continuous_domRestrict.mpr hrestr
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hr.continuousOn
    change Tendsto (radialMap r) (𝓝 0) (𝓝 (radialMap r 0))
    rw [radialMap_zero]
    apply squeeze_zero_norm (a := fun x : E => C * ‖x‖)
    · intro x
      obtain ⟨p, hp⟩ := exists_eq_norm_smul x
      conv_lhs => rw [hp]
      rw [radialMap_smul r p (norm_nonneg x), norm_smul,
        norm_eq_of_mem_sphere p, mul_one, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (norm_nonneg x)]
      have hb := hC p (mem_univ p)
      rw [Real.norm_eq_abs] at hb
      exact mul_le_mul_of_nonneg_right hb (norm_nonneg x)
    · simpa using tendsto_const_nhds.mul (tendsto_norm (x := (0 : E)))
  · exact hon.continuousAt (isOpen_compl_singleton.mem_nhds hx)


def radialHomeomorph (r : sphere (0 : E) 1 → Real) (hr : Continuous r)
    (hpos : ∀ p, 0 < r p) : E ≃ₜ E where
  toFun := radialMap r
  invFun := radialMap (fun p => (r p)⁻¹)
  left_inv x := by
    obtain ⟨p, hp⟩ := exists_eq_norm_smul x
    rw [hp, radialMap_smul r p (norm_nonneg x),
      radialMap_smul (fun p => (r p)⁻¹) p (mul_nonneg (hpos p).le (norm_nonneg x))]
    rw [← mul_assoc, inv_mul_cancel₀ (hpos p).ne', one_mul]
  right_inv x := by
    obtain ⟨p, hp⟩ := exists_eq_norm_smul x
    rw [hp, radialMap_smul (fun p => (r p)⁻¹) p (norm_nonneg x),
      radialMap_smul r p (mul_nonneg (inv_nonneg.mpr (hpos p).le) (norm_nonneg x))]
    rw [← mul_assoc, mul_inv_cancel₀ (hpos p).ne', one_mul]
  continuous_toFun := continuous_radialMap hr
  continuous_invFun := continuous_radialMap (hr.inv₀ (fun p => (hpos p).ne'))


def radialClosedBody (r : sphere (0 : E) 1 → Real) : Set E :=
  {x | ∃ p : sphere (0 : E) 1, ∃ t : Real, 0 ≤ t ∧ t ≤ r p ∧ x = t • (p : E)}


def radialOpenBody (r : sphere (0 : E) 1 → Real) : Set E :=
  {x | ∃ p : sphere (0 : E) 1, ∃ t : Real, 0 ≤ t ∧ t < r p ∧ x = t • (p : E)}

theorem radialHomeomorph_image_closedBall
    (r : sphere (0 : E) 1 → Real) (hr : Continuous r) (hpos : ∀ p, 0 < r p) :
    radialHomeomorph r hr hpos '' closedBall 0 1 = radialClosedBody r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨p, hp⟩ := exists_eq_norm_smul y
    refine ⟨p, r p * ‖y‖, mul_nonneg (hpos p).le (norm_nonneg y), ?_, ?_⟩
    · have hn : ‖y‖ ≤ 1 := by simpa using hy
      simpa using mul_le_mul_of_nonneg_left hn (hpos p).le
    · change radialMap r y = _
      conv_lhs => rw [hp]
      exact radialMap_smul r p (norm_nonneg y)
  · rintro ⟨p, t, ht, htr, rfl⟩
    refine ⟨(t / r p) • (p : E), ?_, ?_⟩
    · simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, abs_of_pos (hpos p)] using
        (div_le_one (hpos p)).mpr htr
    · change radialMap r ((t / r p) • (p : E)) = _
      rw [radialMap_smul r p (div_nonneg ht (hpos p).le), mul_div_cancel₀ t (hpos p).ne']

theorem radialHomeomorph_image_ball
    (r : sphere (0 : E) 1 → Real) (hr : Continuous r) (hpos : ∀ p, 0 < r p) :
    radialHomeomorph r hr hpos '' ball 0 1 = radialOpenBody r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨p, hp⟩ := exists_eq_norm_smul y
    refine ⟨p, r p * ‖y‖, mul_nonneg (hpos p).le (norm_nonneg y), ?_, ?_⟩
    · have hn : ‖y‖ < 1 := by simpa using hy
      simpa using mul_lt_mul_of_pos_left hn (hpos p)
    · change radialMap r y = _
      conv_lhs => rw [hp]
      exact radialMap_smul r p (norm_nonneg y)
  · rintro ⟨p, t, ht, htr, rfl⟩
    refine ⟨(t / r p) • (p : E), ?_, ?_⟩
    · simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, abs_of_pos (hpos p)] using
        (div_lt_one (hpos p)).mpr htr
    · change radialMap r ((t / r p) • (p : E)) = _
      rw [radialMap_smul r p (div_nonneg ht (hpos p).le), mul_div_cancel₀ t (hpos p).ne']

theorem radialHomeomorph_image_sphere
    (r : sphere (0 : E) 1 → Real) (hr : Continuous r) (hpos : ∀ p, 0 < r p) :
    radialHomeomorph r hr hpos '' sphere 0 1 =
      range (fun p : sphere (0 : E) 1 => r p • (p : E)) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, (radialMap_sphere r ⟨p, hp⟩).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, p.property, radialMap_sphere r p⟩

end Poincare.Topology
