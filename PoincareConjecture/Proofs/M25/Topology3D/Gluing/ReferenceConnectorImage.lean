import PoincareConjecture.Proofs.M25.Topology3D.Services
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic











set_option autoImplicit false

open Set Function
open scoped Matrix

namespace PoincareConjecture.M25.Topology3D




theorem saddle_reference_connector_image
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (rho delta : ℝ) (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta ≤ rho ^ 2 / 128)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (ks : OpenPartialHomeomorph E2 UnitTwoSphere)
    (hksForm : ∀ x : E2, ks x = e.symm (N (rho • J2 x))) :
    let mu := delta / rho ^ 2
    let sign : Fin 2 → ℝ := ![1, -1]
    let Z : Fin 2 → Set E2 := fun i =>
      {x | ‖x‖ ≤ 1 ∧
        (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu)}
    let aa := Real.sqrt ((rho ^ 2 - delta) / 2)
    let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
    let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t =>
      e.symm (N
        (sign i * vv t, sign i * Real.sqrt ((vv t) ^ 2 + delta)))
    ∀ i : Fin 2, ks '' Z i = range (gamma i) := by
  let mu := delta / rho ^ 2
  let sign : Fin 2 → ℝ := ![1, -1]
  let Z : Fin 2 → Set E2 := fun i =>
    {x | ‖x‖ ≤ 1 ∧
      (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu)}
  let aa := Real.sqrt ((rho ^ 2 - delta) / 2)
  let vv : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let gamma : Fin 2 → unitInterval → UnitTwoSphere := fun i t =>
    e.symm (N
      (sign i * vv t, sign i * Real.sqrt ((vv t) ^ 2 + delta)))
  change ∀ i : Fin 2, ks '' Z i = range (gamma i)
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hmu : 0 < mu := div_pos hdelta hrho2
  have hmuSmall : mu ≤ 1 / 128 :=
    (div_le_iff₀ hrho2).mpr (by linarith)
  have hmuOne : mu < 1 := by linarith
  have hmurho : rho ^ 2 * mu = delta := by
    dsimp only [mu]
    field_simp
  have hsign (i : Fin 2) : (sign i) ^ 2 = 1 := by
    fin_cases i <;> norm_num [sign]
  let s := Real.sqrt ((1 - mu) / 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hs2 : s ^ 2 = (1 - mu) / 2 := Real.sq_sqrt (by linarith)
  let w : unitInterval → ℝ := fun t => s * (1 - 2 * (t : ℝ))
  let normal : Fin 2 → unitInterval → E2 := fun i t =>
    J2.symm (sign i * w t, sign i * Real.sqrt ((w t) ^ 2 + mu))
  have hnormal (i : Fin 2) (t : unitInterval) : normal i t ∈ Z i := by
    have ht : (1 - 2 * (t : ℝ)) ^ 2 ≤ 1 := by
      nlinarith [t.property.1, t.property.2]
    have hw : (w t) ^ 2 ≤ s ^ 2 := by
      calc
        (w t) ^ 2 = s ^ 2 * (1 - 2 * (t : ℝ)) ^ 2 := by dsimp [w]; ring
        _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left ht (sq_nonneg s)
        _ = s ^ 2 := mul_one _
    have hrad : 0 ≤ (w t) ^ 2 + mu := by positivity
    have hn : ‖normal i t‖ ^ 2 = 2 * (w t) ^ 2 + mu := by
      calc
        ‖normal i t‖ ^ 2 = (J2 (normal i t)).1 ^ 2 +
            (J2 (normal i t)).2 ^ 2 := (hJ2 (normal i t)).symm
        _ = 2 * (w t) ^ 2 + mu := by
          simp only [normal, J2.apply_symm_apply, mul_pow, hsign i, one_mul,
            Real.sq_sqrt hrad]
          ring
    refine ⟨by nlinarith [norm_nonneg (normal i t)], ?_⟩
    simp only [normal, J2.apply_symm_apply, mul_pow, hsign i, one_mul]
  have hparam (i : Fin 2) (x : E2) (hx : x ∈ Z i) :
      ∃ t : unitInterval, normal i t = x := by
    change ‖x‖ ≤ 1 ∧
      (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu) at hx
    have hrad : 0 ≤ (J2 x).1 ^ 2 + mu := by positivity
    have hn : ‖x‖ ^ 2 = 2 * (J2 x).1 ^ 2 + mu := by
      rw [← hJ2 x, hx.2, mul_pow, hsign i, one_mul, Real.sq_sqrt hrad]
      ring
    have hnorm2 : ‖x‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg x) zero_le_one).mpr hx.1
    let r := sign i * (J2 x).1
    have hr2 : r ^ 2 = (J2 x).1 ^ 2 := by
      dsimp only [r]
      rw [mul_pow, hsign i, one_mul]
    have hrs : r ^ 2 ≤ s ^ 2 := by nlinarith
    have hrabs : |r| ≤ s := (sq_le_sq₀ (abs_nonneg r) hs.le).mp
      (by simpa only [sq_abs] using hrs)
    have hrlo : -1 ≤ r / s := (le_div_iff₀ hs).mpr (by linarith [(abs_le.mp hrabs).1])
    have hrhi : r / s ≤ 1 := (div_le_iff₀ hs).mpr (by linarith [(abs_le.mp hrabs).2])
    let t : unitInterval := ⟨(1 - r / s) / 2, ⟨by linarith, by linarith⟩⟩
    have hwt : w t = r := by
      dsimp only [w, t]
      field_simp [hs.ne']
      ring
    refine ⟨t, ?_⟩
    apply J2.injective
    simp only [normal, J2.apply_symm_apply, hwt]
    apply Prod.ext
    · change sign i * r = (J2 x).1
      calc
        sign i * r = (sign i) ^ 2 * (J2 x).1 := by dsimp [r]; ring
        _ = (J2 x).1 := by rw [hsign i, one_mul]
    · change sign i * Real.sqrt (r ^ 2 + mu) = (J2 x).2
      rw [hr2]
      exact hx.2.symm
  have hscale (v : ℝ) : Real.sqrt (rho ^ 2 * v) = rho * Real.sqrt v := by
    rw [Real.sqrt_mul (sq_nonneg rho), Real.sqrt_sq hrho.le]
  have haa : aa = rho * s := by
    have he : (rho ^ 2 - delta) / 2 = rho ^ 2 * ((1 - mu) / 2) := by
      nlinarith [hmurho]
    change Real.sqrt ((rho ^ 2 - delta) / 2) = rho * Real.sqrt ((1 - mu) / 2)
    rw [he, hscale]
  have hvv (t : unitInterval) : vv t = rho * w t := by
    dsimp only [vv, w]
    rw [haa]
    ring
  have hroot (t : unitInterval) :
      Real.sqrt ((vv t) ^ 2 + delta) = rho * Real.sqrt ((w t) ^ 2 + mu) := by
    have he : (vv t) ^ 2 + delta = rho ^ 2 * ((w t) ^ 2 + mu) := by
      rw [hvv]
      nlinarith [hmurho]
    rw [he, hscale]
  have hnative (i : Fin 2) (t : unitInterval) : ks (normal i t) = gamma i t := by
    change ks (normal i t) = e.symm
      (N (sign i * vv t, sign i * Real.sqrt ((vv t) ^ 2 + delta)))
    rw [hksForm]
    simp only [normal, J2.apply_symm_apply]
    apply congrArg e.symm
    apply congrArg N
    apply Prod.ext
    · change rho * (sign i * w t) = sign i * vv t
      rw [hvv]
      ring
    · change rho * (sign i * Real.sqrt ((w t) ^ 2 + mu)) =
        sign i * Real.sqrt ((vv t) ^ 2 + delta)
      rw [hroot]
      ring
  intro i
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht⟩ := hparam i x hx
    exact ⟨t, (hnative i t).symm.trans (congrArg ks ht)⟩
  · rintro ⟨t, rfl⟩
    exact ⟨normal i t, hnormal i t, hnative i t⟩

end PoincareConjecture.M25.Topology3D
