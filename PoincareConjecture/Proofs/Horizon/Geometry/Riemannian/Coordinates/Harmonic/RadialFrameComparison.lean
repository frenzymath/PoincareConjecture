import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


theorem inner_eq_inner_frame_inverse (x : EuclideanSpace ℝ (Fin n))
    {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsInvertible)
    (hiso : ∀ v w, g.inner x (T v) (T w) = inner ℝ v w)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.inner x v w = inner ℝ (T.inverse v) (T.inverse w) := by
  simpa only [hT.self_apply_inverse] using hiso (T.inverse v) (T.inverse w)


theorem inner_self_sub_norm_sq_le_of_frame_inverse (x : EuclideanSpace ℝ (Fin n))
    {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsInvertible)
    (hiso : ∀ v w, g.inner x (T v) (T w) = inner ℝ v w)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ v, ‖T.inverse v - v‖ ≤ δ * ‖v‖)
    (v : EuclideanSpace ℝ (Fin n)) :
    |g.inner x v v - ‖v‖ ^ 2| ≤ δ * (2 + δ) * ‖v‖ ^ 2 := by
  have habs : |‖T.inverse v‖ - ‖v‖| ≤ δ * ‖v‖ :=
    (abs_norm_sub_norm_le _ _).trans (hclose v)
  have hsum : ‖T.inverse v‖ + ‖v‖ ≤ (2 + δ) * ‖v‖ := by
    have h := (norm_sub_norm_le (T.inverse v) v).trans (hclose v)
    linarith
  rw [inner_eq_inner_frame_inverse x hT hiso, real_inner_self_eq_norm_sq,
    show ‖T.inverse v‖ ^ 2 - ‖v‖ ^ 2 =
      (‖T.inverse v‖ - ‖v‖) * (‖T.inverse v‖ + ‖v‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ (δ * ‖v‖) * ((2 + δ) * ‖v‖) :=
      mul_le_mul habs hsum (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg hδ (norm_nonneg _))
    _ = _ := by ring



private theorem tangentNorm_le_of_inner_self_le (x : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin n)) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (hlower : a * ‖z‖ ^ 2 ≤ g.inner x z z)
    (hdual : g.inner x z z ≤ c * ‖z‖) :
    g.tangentNorm x z ≤ c / Real.sqrt a := by
  have hnorm : ‖z‖ ≤ c / a := by
    by_cases hz : z = 0
    · simp only [hz, norm_zero]
      positivity
    · have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
      apply (le_div_iff₀ ha).mpr
      have h := hlower.trans hdual
      nlinarith
  have henergy : g.inner x z z ≤ c ^ 2 / a := by
    calc
      _ ≤ c * ‖z‖ := hdual
      _ ≤ c * (c / a) := mul_le_mul_of_nonneg_left hnorm hc
      _ = _ := by ring
  have h := Real.sqrt_le_sqrt henergy
  simpa only [RiemannianMetric.tangentNorm, Real.sqrt_div (sq_nonneg c),
    Real.sqrt_sq hc] using h



theorem gradient_linear_sub_frame_norm_le (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n))
    {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsInvertible)
    (hiso : ∀ v w, g.inner x (T v) (T w) = inner ℝ v w)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hclose : ∀ v, ‖T.inverse v - v‖ ≤ δ * ‖v‖)
    (e : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm x ((show EuclideanSpace ℝ (Fin n) from
      D.gradient (innerSL ℝ e) x) - T e) ≤ δ * ‖e‖ / Real.sqrt a := by
  let z : EuclideanSpace ℝ (Fin n) :=
    (show EuclideanSpace ℝ (Fin n) from D.gradient (innerSL ℝ e) x) - T e
  have hframe (v : EuclideanSpace ℝ (Fin n)) :
      g.inner x (T e) v = inner ℝ e (T.inverse v) := by
    simpa only [hT.self_apply_inverse] using hiso e (T.inverse v)
  have hgrad (v : EuclideanSpace ℝ (Fin n)) :
      g.inner x (D.gradient (innerSL ℝ e) x) v = inner ℝ e v := by
    rw [D.inner_gradient]
    have hmf : mvfderiv (𝓡 n) (innerSL ℝ e) x = fderiv ℝ (innerSL ℝ e) x := by
      ext u
      simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
      rfl
    rw [hmf, ContinuousLinearMap.fderiv]
    rfl
  have hdual (v : EuclideanSpace ℝ (Fin n)) :
      g.inner x z v = inner ℝ e (v - T.inverse v) := by
    change g.inner x (D.gradient (innerSL ℝ e) x -
      (show TangentSpace (𝓡 n) x from T e)) v = _
    rw [map_sub, sub_apply, hgrad, hframe, inner_sub_right]
  have hbound : g.inner x z z ≤ (δ * ‖e‖) * ‖z‖ := by
    rw [hdual]
    calc
      _ ≤ |inner ℝ e (z - T.inverse z)| := le_abs_self _
      _ ≤ ‖e‖ * ‖z - T.inverse z‖ := abs_real_inner_le_norm _ _
      _ = ‖e‖ * ‖T.inverse z - z‖ := by rw [norm_sub_rev]
      _ ≤ ‖e‖ * (δ * ‖z‖) := mul_le_mul_of_nonneg_left (hclose z) (norm_nonneg _)
      _ = _ := by ring
  exact tangentNorm_le_of_inner_self_le x z ha (mul_nonneg hδ (norm_nonneg e))
    (hlower z) hbound


theorem gradient_coordinate_sub_frame_norm_le (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n))
    {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsInvertible)
    (hiso : ∀ v w, g.inner x (T v) (T w) = inner ℝ v w)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hclose : ∀ v, ‖T.inverse v - v‖ ≤ δ * ‖v‖)
    (i : Fin n) :
    g.tangentNorm x ((show EuclideanSpace ℝ (Fin n) from
      D.gradient (fun y => y i) x) - T (EuclideanSpace.basisFun (Fin n) ℝ i)) ≤
        δ / Real.sqrt a := by
  have hlinear : (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) :
      EuclideanSpace ℝ (Fin n) → ℝ) = fun y => y i := by
    funext y
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simpa only [hlinear, OrthonormalBasis.norm_eq_one, mul_one] using
    gradient_linear_sub_frame_norm_le D x hT hiso ha hδ hlower hclose
      (EuclideanSpace.basisFun (Fin n) ℝ i)

end PoincareConjecture.HarmonicCoordinates
