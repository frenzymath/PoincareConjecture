import PoincareConjecture.Proofs.M35.Uniqueness.RotationRadialSplit
import PoincareConjecture.Proofs.M35.Uniqueness.KillingGradientEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

variable {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hsec : D.NonnegativeSectionalCurvature) (hcomplete : MetricComplete g)

include hrotation hsec hcomplete

theorem rotational_linear_skew_derivative_bound
    (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (hB : ∀ x, inner ℝ x (B x) = 0)
    {x : StandardCapSpace} (hx : x ≠ 0) (u : StandardCapSpace) :
    g.inner x (D.connection (fun z => B z) x u) (D.connection (fun z => B z) x u) ≤
      3 * ‖B‖ ^ 2 * g.inner x u u := by
  let r := ‖x‖
  have hr : 0 < r := norm_pos_iff.mpr hx
  let n : StandardCapSpace := r⁻¹ • x
  have hn : ‖n‖ = 1 := by
    change ‖r⁻¹ • x‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  have hxn : x = r • n := by
    dsimp only [n]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  let p := inner ℝ n u
  let y : StandardCapSpace := u - p • n
  have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have hy : inner ℝ n y = 0 := by
    dsimp only [y, p]
    rw [inner_sub_right, inner_smul_right, hnn, mul_one, sub_self]
  have hu : p • n + y = u := by dsimp only [y]; abel
  have hu' : y + p • n = u := sub_add_cancel _ _
  let l := 1 + r ^ 2 * radialConnectionAlpha g r
  let q := inner ℝ n (B y)
  let z : StandardCapSpace := (l * p) • B n + (B y - q • n)
  have hz : inner ℝ n z = 0 := by
    dsimp only [z, q]
    rw [inner_add_right, inner_smul_right, hB n, mul_zero,
      inner_sub_right, inner_smul_right, hnn, mul_one, sub_self, add_zero]
  have hconn := rotational_connection_skew_radial_split hrotation D B hB hr hn hxn y p hy
  rw [hu] at hconn
  have hgout := rotational_metric_split_normSq hrotation hr hn hxn z
    ((axisAngularCoefficient g r * l / axisRadialCoefficient g r) * q) hz
  have hgin := rotational_metric_split_normSq hrotation hr hn hxn y p hy
  rw [hu'] at hgin
  have he := rotation_weighted_energy_bound B hn y (p := p)
    (axisAngularCoefficient_pos g r) (axisRadialCoefficient_pos g r)
    (radialConnection_alpha_weighted_bound D hrotation hsec hcomplete hr)
  rw [hconn]
  change g.inner x
    (z + ((axisAngularCoefficient g r * l / axisRadialCoefficient g r) * q) • n)
    (z + ((axisAngularCoefficient g r * l / axisRadialCoefficient g r) * q) • n) ≤ _
  rw [hgout, hgin]
  rw [add_comm (axisAngularCoefficient g r * ‖y‖ ^ 2)
    (axisRadialCoefficient g r * p ^ 2)]
  exact he

theorem rotational_linear_skew_gradient_normSq_le
    (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (hB : ∀ x, inner ℝ x (B x) = 0) (x : StandardCapSpace) :
    (g.tensorNorm (D.covariantTensorDerivative (killingCovector g (fun z => B z))) x) ^ 2 ≤
      9 * ‖B‖ ^ 2 := by
  have hcontinuous := (M04.contMDiff_tensorNorm_sq g
    (M04.isSmoothCovariantTensor_covariantTensorDerivative D
      (isSmoothCovariantTensor_killingCovector g _ B.contDiff))).continuous
  have hclosed := isClosed_le hcontinuous (continuous_const (y := 9 * ‖B‖ ^ 2))
  have hbound : ({(0 : StandardCapSpace)}ᶜ : Set StandardCapSpace) ⊆
      {y | (g.tensorNorm (D.covariantTensorDerivative
        (killingCovector g (fun z => B z))) y) ^ 2 ≤ 9 * ‖B‖ ^ 2} := by
    intro y hy
    have hy0 : y ≠ 0 := hy
    change (g.tensorNorm (D.covariantTensorDerivative (killingCovector g (fun z => B z))) y) ^ 2 ≤ _
    rw [killingCovectorGradient_normSq D _ B.contDiff]
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hb (i) : g.inner y (g.orthonormalBasis y i) (g.orthonormalBasis y i) = 1 := by
      change inner ℝ (g.orthonormalBasis y i) (g.orthonormalBasis y i) = 1
      rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis y).norm_eq_one, one_pow]
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) y) = 3 := finrank_euclideanSpace_fin
    calc
      _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) y)), 3 * ‖B‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [hb, mul_one] using
          rotational_linear_skew_derivative_bound D hrotation hsec hcomplete B hB hy0
            (g.orthonormalBasis y i)
      _ = _ := by simp [hdim]; ring
  have hext := closure_minimal hbound hclosed
  rw [closure_compl_singleton] at hext
  exact hext (mem_univ x)

end PoincareConjecture.M35.Uniqueness
