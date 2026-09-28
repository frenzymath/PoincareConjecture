import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LowerCaps

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

def upperAbscissa (t : Real) : Real := t / Real.sqrt (1 + Real.sqrt (1 + t^2))

theorem upperAbscissa_sq (t : Real) :
    upperAbscissa t ^ 2 = Real.sqrt (1 + t^2) - 1 := by
  have hp : 0 < 1 + Real.sqrt (1 + t^2) := by positivity
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1 + t^2)
  unfold upperAbscissa
  rw [div_pow, Real.sq_sqrt hp.le]
  apply (div_eq_iff hp.ne').mpr
  nlinarith

theorem upperAbscissa_identity (t : Real) :
    (upperAbscissa t)^4 + 2 * (upperAbscissa t)^2 = t^2 := by
  have hs := upperAbscissa_sq t
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ 1 + t^2)
  nlinarith [sq_nonneg (upperAbscissa t)]

theorem upperAbscissa_contDiff : ContDiff Real ∞ upperAbscissa := by
  unfold upperAbscissa
  exact contDiff_id.div
    ((contDiff_const.add ((contDiff_const.add (contDiff_id.pow 2)).sqrt
      (fun t => ne_of_gt (by positivity)))).sqrt (fun t => ne_of_gt (by positivity)))
    (fun t => ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

theorem upperAbscissa_coordinate (t : Real) :
    upperAbscissa t * Real.sqrt ((upperAbscissa t)^2 + 2) = t := by
  have heq : (upperAbscissa t)^2 + 2 = 1 + Real.sqrt (1+t^2) := by
    rw [upperAbscissa_sq]
    ring
  rw [heq]
  exact div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

theorem upperAbscissa_inverse (x : Real) :
    upperAbscissa (x * Real.sqrt (x^2+2)) = x := by
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ x^2+2)
  have heq : 1 + (x * Real.sqrt (x^2+2))^2 = (x^2+1)^2 := by
    rw [mul_pow, hroot]
    ring
  unfold upperAbscissa
  rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < x^2+1),
    show 1 + (x^2+1) = x^2+2 by ring]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

def upperCap (q : E2) : E3 :=
  vector (upperAbscissa (q 0)) (q 1)
    (Real.sqrt (1 - (upperAbscissa (q 0))^2 - (q 1)^2) - (upperAbscissa (q 0))^2)

theorem upperCap_radicand_pos {q : E2} (hq : q ∈ ball (0 : E2) 1) :
    0 < 1 - (upperAbscissa (q 0))^2 - (q 1)^2 := by
  have hn := mem_ball_zero_iff.mp hq
  have hid := upperAbscissa_identity (q 0)
  have hnorm := norm_sq_two q
  have hs := sq_nonneg (upperAbscissa (q 0))
  have hs4 := sq_nonneg ((upperAbscissa (q 0))^2)
  nlinarith [norm_nonneg q]

theorem upperCap_contDiffOn : ContDiffOn Real ∞ upperCap (ball (0 : E2) 1) := by
  have hx : ContDiff Real ∞ (fun q : E2 => upperAbscissa (q 0)) :=
    upperAbscissa_contDiff.comp (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
  have hy : ContDiff Real ∞ (fun q : E2 => q 1) :=
    (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
  have hz : ContDiffOn Real ∞
      (fun q : E2 => Real.sqrt (1 - (upperAbscissa (q 0))^2 - (q 1)^2) -
        (upperAbscissa (q 0))^2) (ball (0 : E2) 1) :=
    (((contDiff_const.sub (hx.pow 2)).sub (hy.pow 2)).contDiffOn.sqrt
      (fun q hq => (upperCap_radicand_pos hq).ne')).sub (hx.pow 2).contDiffOn
  have hvec (x y z : Real) : vector x y z =
      x • EuclideanSpace.single 0 1 + y • EuclideanSpace.single 1 1 +
        z • EuclideanSpace.single 2 1 := by
    ext i
    fin_cases i <;> simp [vector]
  unfold upperCap
  simp only [hvec]
  exact ((hx.contDiffOn.smul contDiffOn_const).add
    (hy.contDiffOn.smul contDiffOn_const)).add (hz.smul contDiffOn_const)

theorem upperCap_mem_surface {q : E2} (hq : q ∈ ball (0 : E2) 1) :
    polynomial (upperCap q) = 1 := by
  unfold polynomial upperCap
  simp only [vector_zero, vector_one, vector_two, sub_add_cancel]
  rw [Real.sq_sqrt (upperCap_radicand_pos hq).le]
  ring

theorem upper_closedBall_subset_domain :
    closedBall (0 : E2) (Real.sqrt (3/4)) ⊆ ball (0 : E2) 1 := by
  intro q hq
  have hn := mem_closedBall_zero_iff.mp hq
  rw [mem_ball_zero_iff]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3/4), Real.sqrt_nonneg (3/4)]

theorem upperCap_height_ge_iff {q : E2} (hq : q ∈ ball (0 : E2) 1) :
    1/2 ≤ upperCap q 2 ↔ ‖q‖^2 ≤ 3/4 := by
  change 1/2 ≤ Real.sqrt (1 - (upperAbscissa (q 0))^2 - (q 1)^2) -
    (upperAbscissa (q 0))^2 ↔ _
  have hs := Real.sq_sqrt (upperCap_radicand_pos hq).le
  have hn := Real.sqrt_nonneg (1 - (upperAbscissa (q 0))^2 - (q 1)^2)
  have hid := upperAbscissa_identity (q 0)
  rw [norm_sq_two]
  constructor <;> intro h
  · nlinarith [sq_nonneg (upperAbscissa (q 0)),
      sq_nonneg (Real.sqrt (1 - (upperAbscissa (q 0))^2 - (q 1)^2) -
        (upperAbscissa (q 0))^2 - 1/2)]
  · nlinarith [sq_nonneg (upperAbscissa (q 0))]

def upperCoordinates (p : E3) : E2 := WithLp.toLp 2 ![p 0 * Real.sqrt ((p 0)^2+2), p 1]

theorem upperCoordinates_contDiff : ContDiff Real ∞ upperCoordinates := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff Real ∞ (fun p : E3 => p 0 * Real.sqrt ((p 0)^2+2))
    exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff.mul
      (((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff.pow 2).add
        contDiff_const |>.sqrt (fun p => ne_of_gt (by positivity)))
  · change ContDiff Real ∞ (fun p : E3 => p 1)
    fun_prop

theorem upperCoordinates_upperCap (q : E2) : upperCoordinates (upperCap q) = q := by
  ext i
  fin_cases i
  · exact upperAbscissa_coordinate (q 0)
  · rfl

theorem upperCap_injective : Injective upperCap :=
  Function.LeftInverse.injective upperCoordinates_upperCap

theorem upperCap_fderiv_injective {q : E2} (hq : q ∈ ball (0 : E2) 1) :
    Injective (fderiv Real upperCap q) := by
  have heq : upperCoordinates ∘ upperCap = id := funext upperCoordinates_upperCap
  have hc := congrArg (fun g : E2 → E2 => fderiv Real g q) heq
  rw [fderiv_comp q (upperCoordinates_contDiff.differentiable (by simp) _)
    (((upperCap_contDiffOn q hq).contDiffAt (isOpen_ball.mem_nhds hq)).differentiableAt
      (by simp)), fderiv_id] at hc
  intro x y hxy
  have h := congrArg (fun L : E2 →L[Real] E2 => L x) hc
  have h' := congrArg (fun L : E2 →L[Real] E2 => L y) hc
  change fderiv Real upperCoordinates (upperCap q) (fderiv Real upperCap q x) = x at h
  change fderiv Real upperCoordinates (upperCap q) (fderiv Real upperCap q y) = y at h'
  rw [hxy] at h
  exact h.symm.trans h'

theorem upperCoordinates_norm_sq (p : E3) :
    ‖upperCoordinates p‖^2 = (p 0)^4 + 2*(p 0)^2 + (p 1)^2 := by
  rw [norm_sq_two]
  change (p 0 * Real.sqrt ((p 0)^2+2))^2 + (p 1)^2 = _
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

theorem upperCap_image_closedBall :
    upperCap '' closedBall (0 : E2) (Real.sqrt (3/4)) =
      {p | polynomial p = 1 ∧ 1/2 ≤ p 2} := by
  apply Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    refine ⟨upperCap_mem_surface (upper_closedBall_subset_domain hq),
      (upperCap_height_ge_iff (upper_closedBall_subset_domain hq)).mpr ?_⟩
    have hn := mem_closedBall_zero_iff.mp hq
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3/4),
      Real.sqrt_nonneg (3/4), norm_nonneg q]
  · intro p hp
    let q := upperCoordinates p
    have hq : q ∈ closedBall (0 : E2) (Real.sqrt (3/4)) := by
      rw [mem_closedBall_zero_iff]
      have hn : ‖q‖^2 = (p 0)^4 + 2*(p 0)^2 + (p 1)^2 := upperCoordinates_norm_sq p
      have hpoly := hp.1
      unfold polynomial at hpoly
      nlinarith [hp.2, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3/4),
        Real.sqrt_nonneg (3/4), norm_nonneg q, sq_nonneg (p 2 - 1/2),
        mul_nonneg (show 0 ≤ p 2 - 1/2 by linarith [hp.2]) (sq_nonneg (p 0))]
    refine ⟨q, hq, ?_⟩
    have hx : upperAbscissa (q 0) = p 0 := upperAbscissa_inverse (p 0)
    have hpoly := hp.1
    unfold polynomial at hpoly
    have hr : 1 - (p 0)^2 - (p 1)^2 = (p 2 + (p 0)^2)^2 := by linarith
    ext i
    fin_cases i
    · exact hx
    · rfl
    · change Real.sqrt (1 - (upperAbscissa (q 0))^2 - (p 1)^2) -
        (upperAbscissa (q 0))^2 = p 2
      rw [hx, hr, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (by nlinarith [hp.2, sq_nonneg (p 0)] : 0 ≤ p 2 + (p 0)^2)]
      ring

theorem upperCap_boundary_height {q : E2}
    (hq : q ∈ sphere (0 : E2) (Real.sqrt (3/4))) : upperCap q 2 = 1/2 := by
  have hq' := upper_closedBall_subset_domain (sphere_subset_closedBall hq)
  have hn : (q 0)^2 + (q 1)^2 = 3/4 := by
    rw [← norm_sq_two, mem_sphere_zero_iff_norm.mp hq, Real.sq_sqrt (by norm_num)]
  have hid := upperAbscissa_identity (q 0)
  have hs := Real.sq_sqrt (upperCap_radicand_pos hq').le
  have hpos := Real.sqrt_nonneg (1 - (upperAbscissa (q 0))^2 - (q 1)^2)
  change Real.sqrt (1 - (upperAbscissa (q 0))^2 - (q 1)^2) -
    (upperAbscissa (q 0))^2 = 1/2
  nlinarith [sq_nonneg (upperAbscissa (q 0))]

theorem upperCap_height_eq_iff {q : E2} (hq : q ∈ ball (0 : E2) 1) :
    upperCap q 2 = 1/2 ↔ ‖q‖^2 = 3/4 := by
  have hid := upperAbscissa_identity (q 0)
  have hs := Real.sq_sqrt (upperCap_radicand_pos hq).le
  have hpos := Real.sqrt_nonneg (1 - (upperAbscissa (q 0))^2 - (q 1)^2)
  change Real.sqrt (1 - (upperAbscissa (q 0))^2 - (q 1)^2) -
    (upperAbscissa (q 0))^2 = 1/2 ↔ _
  rw [norm_sq_two]
  constructor <;> intro h <;> nlinarith [sq_nonneg (upperAbscissa (q 0))]

end Poincare.Manifold.Schoenflies.Saddle
