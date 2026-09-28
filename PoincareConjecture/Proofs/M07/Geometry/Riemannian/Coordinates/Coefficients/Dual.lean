import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.InverseEstimate
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))

noncomputable def inverseCoefficients
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  EuclideanSpace.proj j ((g.inner x).inverse (EuclideanSpace.proj i))

lemma contDiff_inverseCoefficients (i j : Fin n) :
    ContDiff ℝ ∞ (fun x ↦ g.inverseCoefficients x i j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hI := (g.inner_isInvertible x).contDiffAt_map_inverse.comp x
    (g.contDiffAt_euclideanCoefficients x)
  have h := (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp x
    (hI.clm_apply (contDiffAt_const (c := EuclideanSpace.proj (𝕜 := ℝ) i)))
  exact h

lemma inverseCoefficients_symm (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    g.inverseCoefficients x i j = g.inverseCoefficients x j i := by
  have h := g.symm x ((g.inner x).inverse (EuclideanSpace.proj i))
    ((g.inner x).inverse (EuclideanSpace.proj j))
  rw [(g.inner_isInvertible x).self_apply_inverse,
    (g.inner_isInvertible x).self_apply_inverse] at h
  exact h.symm

lemma sum_inverseCoefficients_mul_eq_inner (x v : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ∑ j, g.inverseCoefficients x i j * v i * v j) =
      inner ℝ v ((g.inner x).inverse (innerSL ℝ v)) := by
  have hdual : innerSL ℝ v = ∑ i, v i • EuclideanSpace.proj i := by
    ext w
    simp [innerSL_apply_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      PiLp.proj_apply, mul_comm]
  rw [hdual, map_sum, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, inner_smul_right]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    Pi.star_apply, Finset.mul_sum, inverseCoefficients, PiLp.proj_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sum_inverseCoefficients_mul_le (x : EuclideanSpace ℝ (Fin n))
    {a : ℝ} (ha : 0 < a)
    (hell : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ∑ j, g.inverseCoefficients x i j * v i * v j) ≤ ‖v‖ ^ 2 / a := by
  rw [g.sum_inverseCoefficients_mul_eq_inner]
  exact CoordinateExponential.inner_inverse_innerSL_le ha hell v

lemma le_sum_inverseCoefficients_mul (x : EuclideanSpace ℝ (Fin n))
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖v‖ ^ 2 / b ≤ ∑ i, ∑ j, g.inverseCoefficients x i j * v i * v j := by
  rw [g.sum_inverseCoefficients_mul_eq_inner]
  exact CoordinateExponential.le_inner_inverse_innerSL ha hb (g.symm x) hlower hupper v

private lemma norm_euclidean_proj (i : Fin n) :
    ‖EuclideanSpace.proj (𝕜 := ℝ) i‖ = 1 := by
  have h : EuclideanSpace.proj (𝕜 := ℝ) i =
      innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) := by
    ext v
    simp only [PiLp.proj_apply, innerSL_apply_apply, EuclideanSpace.basisFun_inner]
  rw [h, innerSL_apply_norm, (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one]

lemma abs_inverseCoefficients_le (x : EuclideanSpace ℝ (Fin n))
    {a : ℝ} (ha : 0 < a)
    (hell : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (i j : Fin n) : |g.inverseCoefficients x i j| ≤ 1 / a := by
  have h := CoordinateExponential.norm_inverse_apply_le_of_ellipticity
    ha hell (EuclideanSpace.proj i)
  rw [norm_euclidean_proj] at h
  have heval := (EuclideanSpace.proj (𝕜 := ℝ) j).le_opNorm
    ((g.inner x).inverse (EuclideanSpace.proj i))
  rw [norm_euclidean_proj, one_mul] at heval
  simpa only [inverseCoefficients, PiLp.proj_apply, Real.norm_eq_abs] using heval.trans h

lemma abs_inverseCoefficients_sub_le (x y : EuclideanSpace ℝ (Fin n))
    {a H r : ℝ} (ha : 0 < a)
    (hx : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hy : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner y v v)
    (hmod : ‖g.euclideanCoefficients x - g.euclideanCoefficients y‖ ≤ H * r)
    (i j : Fin n) :
    |g.inverseCoefficients x i j - g.inverseCoefficients y i j| ≤ (H / a ^ 2) * r := by
  have h := CoordinateExponential.norm_inverse_sub_le_of_modulus ha hx hy hmod
  have happly := ((g.euclideanCoefficients x).inverse -
    (g.euclideanCoefficients y).inverse).le_opNorm (EuclideanSpace.proj i)
  rw [norm_euclidean_proj, mul_one] at happly
  have heval := (EuclideanSpace.proj (𝕜 := ℝ) j).le_opNorm
    (((g.euclideanCoefficients x).inverse -
      (g.euclideanCoefficients y).inverse) (EuclideanSpace.proj i))
  rw [norm_euclidean_proj, one_mul] at heval
  have hfinal := heval.trans (happly.trans h)
  simp only [inverseCoefficients, euclideanCoefficients, sub_apply, map_sub,
    PiLp.proj_apply, Real.norm_eq_abs] at hfinal ⊢
  convert! hfinal using 1

end PoincareConjecture.RiemannianMetric
