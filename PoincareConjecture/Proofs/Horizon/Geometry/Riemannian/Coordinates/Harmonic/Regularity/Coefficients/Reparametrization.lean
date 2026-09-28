import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Inverse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Perturbation









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.HarmonicCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem norm_fderiv_symm_and_sub_id_le
    {β : ℝ} (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2)
    (F : OpenPartialHomeomorph E E) (hF : ContDiffOn ℝ ∞ F F.source)
    {x : E} (hx : x ∈ F.target)
    (hclose : ‖fderiv ℝ F (F.symm x) - ContinuousLinearMap.id ℝ E‖ ≤ β) :
    ‖fderiv ℝ F.symm x‖ ≤ 2 ∧
      ‖fderiv ℝ F.symm x - ContinuousLinearMap.id ℝ E‖ ≤ 2 * β := by
  have hdiff := (hF.contDiffAt (F.open_source.mem_nhds (F.map_target hx))).differentiableAt
    (by simp)
  obtain ⟨A, hA⟩ := isInvertible_of_norm_sub_id_le_half (hclose.trans hβhalf)
  have hderiv : HasFDerivAt F (A : E →L[ℝ] E) (F.symm x) := by
    simpa only [hA] using hdiff.hasFDerivAt
  have hAclose : ‖(A : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E‖ ≤ β := by
    rw [hA]
    exact hclose
  have hnorm (v : E) : ‖A.symm v‖ ≤ 2 * ‖v‖ := by
    have h := (norm_apply_bounds_of_norm_sub_id_le_half
      (hAclose.trans hβhalf) (A.symm v)).1
    simp only [ContinuousLinearEquiv.coe_coe, A.apply_symm_apply] at h
    linarith
  have herror (v : E) : ‖A.symm v - v‖ ≤ (2 * β) * ‖v‖ := by
    calc
      _ = ‖((A : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E) (A.symm v)‖ := by
        simp only [sub_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearEquiv.coe_coe, A.apply_symm_apply, norm_sub_rev]
      _ ≤ ‖(A : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E‖ * ‖A.symm v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ β * (2 * ‖v‖) := mul_le_mul hAclose (hnorm v) (norm_nonneg _) hβ
      _ = (2 * β) * ‖v‖ := by ring
  rw [(F.hasFDerivAt_symm hx hderiv).fderiv]
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    exact hnorm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    simpa only [sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe] using herror v

end PoincareConjecture.HarmonicCoordinates

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ}



theorem inverse_pullback_quadratic_error_le
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (hF : ContDiffOn ℝ ∞ F F.source)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ F.target)
    (hmetric : ∀ v : EuclideanSpace ℝ (Fin n),
      |g.euclideanCoefficients (F.symm x) v v - ‖v‖ ^ 2| ≤ α * ‖v‖ ^ 2)
    (hclose : ‖fderiv ℝ F (F.symm x) -
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ β)
    (v : EuclideanSpace ℝ (Fin n)) :
    |g.pullbackCoefficients F.symm x v v - ‖v‖ ^ 2| ≤ (4 * α + 6 * β) * ‖v‖ ^ 2 := by
  let A := fderiv ℝ F.symm x
  obtain ⟨hAnorm, hAerror⟩ :=
    HarmonicCoordinates.norm_fderiv_symm_and_sub_id_le hβ hβhalf F hF hx hclose
  have hAv : ‖A v‖ ≤ 2 * ‖v‖ :=
    (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hAnorm (norm_nonneg v))
  have hAvsq : ‖A v‖ ^ 2 ≤ 4 * ‖v‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg (A v))
      (by positivity : 0 ≤ 2 * ‖v‖)).mpr hAv
    nlinarith only [h]
  have hAvdiff : ‖A v - v‖ ≤ (2 * β) * ‖v‖ := by
    exact ((A - ContinuousLinearMap.id ℝ _).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hAerror (norm_nonneg v))
  have hnormdiff : |‖A v‖ ^ 2 - ‖v‖ ^ 2| ≤ (6 * β) * ‖v‖ ^ 2 := by
    have hsub := (abs_norm_sub_norm_le (A v) v).trans hAvdiff
    have hsum : ‖A v‖ + ‖v‖ ≤ 3 * ‖v‖ := by linarith
    rw [show ‖A v‖ ^ 2 - ‖v‖ ^ 2 = (‖A v‖ - ‖v‖) * (‖A v‖ + ‖v‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      _ ≤ ((2 * β) * ‖v‖) * (3 * ‖v‖) :=
        mul_le_mul hsub hsum (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      _ = (6 * β) * ‖v‖ ^ 2 := by ring
  have hval : g.pullbackCoefficients F.symm x v v =
      g.euclideanCoefficients (F.symm x) (A v) (A v) := by
    change g.inner _ (mfderiv _ _ _ _ _) (mfderiv _ _ _ _ _) = _
    rw [mfderiv_eq_fderiv]
    rfl
  calc
    _ = |(g.euclideanCoefficients (F.symm x) (A v) (A v) - ‖A v‖ ^ 2) +
        (‖A v‖ ^ 2 - ‖v‖ ^ 2)| := by rw [hval]; congr 1; ring
    _ ≤ |g.euclideanCoefficients (F.symm x) (A v) (A v) - ‖A v‖ ^ 2| +
        |‖A v‖ ^ 2 - ‖v‖ ^ 2| := by
      simpa only [Real.norm_eq_abs] using norm_add_le
        (g.euclideanCoefficients (F.symm x) (A v) (A v) - ‖A v‖ ^ 2)
        (‖A v‖ ^ 2 - ‖v‖ ^ 2)
    _ ≤ α * ‖A v‖ ^ 2 + (6 * β) * ‖v‖ ^ 2 := add_le_add (hmetric (A v)) hnormdiff
    _ ≤ α * (4 * ‖v‖ ^ 2) + (6 * β) * ‖v‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hAvsq hα) le_rfl
    _ = (4 * α + 6 * β) * ‖v‖ ^ 2 := by ring



theorem norm_inverse_pullback_sub_innerSL_le
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (hF : ContDiffOn ℝ ∞ F F.source)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ F.target)
    (hmetric : ∀ v : EuclideanSpace ℝ (Fin n),
      |g.euclideanCoefficients (F.symm x) v v - ‖v‖ ^ 2| ≤ α * ‖v‖ ^ 2)
    (hclose : ‖fderiv ℝ F (F.symm x) -
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ β) :
    let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
    ‖g.pullbackCoefficients F.symm x - B₀‖ ≤ 4 * α + 6 * β := by
  dsimp only
  apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ (by positivity)
  · intro u v
    change g.inner _ (mfderiv _ _ _ _ u) (mfderiv _ _ _ _ v) - inner ℝ u v =
      g.inner _ (mfderiv _ _ _ _ v) (mfderiv _ _ _ _ u) - inner ℝ v u
    rw [g.symm, real_inner_comm]
  · intro v
    change |g.pullbackCoefficients F.symm x v v - inner ℝ v v| ≤ _
    rw [real_inner_self_eq_norm_sq]
    exact inverse_pullback_quadratic_error_le hα hβ hβhalf g F hF hx hmetric hclose v



theorem norm_inverse_pullback_sub_innerSL_le_of_norm
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hβhalf : β ≤ 1 / 2)
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (hF : ContDiffOn ℝ ∞ F F.source)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ F.target) :
    let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
    ‖g.euclideanCoefficients (F.symm x) - B₀‖ ≤ α →
    ‖fderiv ℝ F (F.symm x) - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ β →
    ‖g.pullbackCoefficients F.symm x - B₀‖ ≤ 4 * α + 6 * β := by
  dsimp only
  intro hmetric hclose
  let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  apply norm_inverse_pullback_sub_innerSL_le hα hβ hβhalf g F hF hx _ hclose
  intro v
  have h := (g.euclideanCoefficients (F.symm x) - B₀).le_opNorm₂ v v
  have h' : ‖g.euclideanCoefficients (F.symm x) - B₀‖ * ‖v‖ * ‖v‖ ≤
      α * ‖v‖ ^ 2 := by
    calc
      _ ≤ α * ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmetric (norm_nonneg v)) (norm_nonneg v)
      _ = _ := by ring
  have hform : B₀ v v = ‖v‖ ^ 2 := by
    change inner ℝ v v = _
    exact real_inner_self_eq_norm_sq v
  simpa only [sub_apply, hform, Real.norm_eq_abs] using h.trans h'

end PoincareConjecture.RiemannianMetric
