import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import Mathlib.Analysis.Calculus.FDeriv.Norm









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators Topology
open Set Filter

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ}

private theorem fderiv_norm_apply_eq {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x v = inner ℝ x v / ‖x‖ := by
  have hn : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v)
    (hn.hasFDerivAt.pow 2).fderiv
  rw [fderiv_norm_sq_apply] at h
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, Nat.cast_ofNat, nsmul_eq_mul,
    Nat.reduceSub, pow_one] at h
  apply (eq_div_iff (norm_ne_zero_iff.mpr hx)).mpr
  linarith


theorem sum_fderiv_mul_coordinate {a : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (ha : DifferentiableAt ℝ a x) :
    (∑ i, fderiv ℝ (fun y => a y * WithLp.ofLp y i) x
      (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      fderiv ℝ a x x + (n : ℝ) * a x := by
  have hi (i : Fin n) :
      fderiv ℝ (fun y => a y * WithLp.ofLp y i) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      fderiv ℝ a x (EuclideanSpace.basisFun (Fin n) ℝ i) * x i + a x := by
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i))
      (ha.hasFDerivAt.mul (EuclideanSpace.proj i).hasFDerivAt).fderiv
    simpa [Pi.mul_def, add_apply, smul_apply, smul_eq_mul,
      EuclideanSpace.basisFun_apply, mul_comm, add_comm] using h
  have hs := congrArg (fderiv ℝ a x)
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr x)
  simp only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr] at hs
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simpa [mul_comm] using congrArg (fun r => r + (n : ℝ) * a x) hs



theorem sum_fderiv_density_radial {ρ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hρ : DifferentiableAt ℝ ρ x) (hx : x ≠ 0) :
    (∑ i, fderiv ℝ (fun y => (ρ y / ‖y‖) * WithLp.ofLp y i) x
      (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      fderiv ℝ ρ x x / ‖x‖ + ((n : ℝ) - 1) * ρ x / ‖x‖ := by
  have hn : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hn.hasFDerivAt
  have ha := hρ.hasFDerivAt.mul hi
  simp only [Pi.mul_def, Function.comp_def] at ha
  simp only [div_eq_mul_inv]
  rw [sum_fderiv_mul_coordinate ha.differentiableAt, ha.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, hn.fderiv_norm_self]
  field_simp
  ring

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem gradient_radial_coordinate (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) (hx0 : x ≠ 0)
    (hgauss : ∀ v : EuclideanSpace ℝ (Fin n),
      g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) = inner ℝ x v) :
    D.gradient (fun y => ‖e.symm y‖) (e x) =
      mfderiv (𝓡 n) (𝓡 n) e x ((‖x‖)⁻¹ • x) := by
  have heDiff : e.MDifferentiable (𝓡 n) (𝓡 n) := ⟨
    fun y hy => (he y hy).mdifferentiableWithinAt (by simp),
    fun y hy => (hei y hy).mdifferentiableWithinAt (by simp)⟩
  have hinv : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible := ⟨heDiff.mfderiv hx, rfl⟩
  have hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => ‖e.symm y‖) (e x) := by
    have hnorm := (contDiffAt_norm ℝ
      (show e.symm (e x) ≠ 0 by simpa only [e.left_inv hx] using hx0) (n := ∞)).contMDiffAt
    exact hnorm.comp (e x) (hei.contMDiffAt (e.open_target.mem_nhds (e.map_source hx)))
  apply (g.inner_isInvertible (e x)).injective
  ext v
  let w := (mfderiv (𝓡 n) (𝓡 n) e x).inverse v
  have hw : mfderiv (𝓡 n) (𝓡 n) e x w = v := hinv.self_apply_inverse v
  have heq : (fun y => ‖e.symm (e y)‖) =ᶠ[𝓝 x]
      (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    rw [e.left_inv hy]
  have hd := congrArg (fun L => L w) (Poincare.mvfderiv_eq_of_eventuallyEq heq)
  change mvfderiv (𝓡 n) ((fun y => ‖e.symm y‖) ∘ e) x w = _ at hd
  rw [mvfderiv_comp x (hu.mdifferentiableAt (by simp)) (heDiff.mdifferentiableAt hx)] at hd
  simp only [ContinuousLinearMap.comp_apply, hw] at hd
  have hnorm : mvfderiv (𝓡 n) (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x w =
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x w := by
    simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  rw [hnorm] at hd
  rw [D.inner_gradient, ← hw, map_smul, map_smul, smul_apply, smul_eq_mul, hgauss]
  rw [← hw] at hd
  rw [hd, fderiv_norm_apply_eq hx0]
  ring

end PoincareConjecture.LeviCivitaData
