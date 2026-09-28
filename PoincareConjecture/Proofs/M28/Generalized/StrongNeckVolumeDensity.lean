import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.DensityBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

open tube

private abbrev E := EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem normalized_neck_chart_density_bounds (N : EpsilonNeck g)
    (hscale : N.scale = 1) (q : UnitTwoSphere) (s : ℝ) {x : E}
    (hx : x ∈ cylinderNeckChartDomain N q s) (hxnorm : ‖x‖ ≤ 1) :
    (1 / 48 : ℝ) ≤ g.pullbackVolumeDensity (cylinderNeckChart N q s) x ∧
      g.pullbackVolumeDensity (cylinderNeckChart N q s) x ≤ 384 := by
  classical
  have hi := (cylinderNeckChart_mfderiv_isInvertible N q s hx).bijective.1
  have hspeed := normalized_neck_chart_speed_bounds N hscale q s hx hxnorm
  obtain ⟨A, hA, hdet⟩ := g.exists_frozenPullbackEquiv hi
  have hinv (v : E) : ‖A.symm v‖ ≤ 2 * ‖v‖ := by
    have h := (hspeed (A.symm v)).1
    rw [← hA, A.apply_symm_apply] at h
    linarith
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hentry (i j : Fin 3) :
      |LinearMap.toMatrix b.toBasis b.toBasis
        A.symm.toContinuousLinearMap.toLinearMap i j| ≤ (2 : ℝ) := by
    rw [LinearMap.toMatrix_apply]
    change |(A.symm (b j)) i| ≤ 2
    calc
      |(A.symm (b j)) i| ≤ ‖A.symm (b j)‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.symm (b j)) i
      _ ≤ 2 * ‖b j‖ := hinv _
      _ = 2 := by simp [b, EuclideanSpace.basisFun_apply]
  have hinvdet : |A.symm.toContinuousLinearMap.det| ≤ (48 : ℝ) := by
    have h := Matrix.det_le (abv := AbsoluteValue.abs) hentry
    rw [LinearMap.det_toMatrix] at h
    norm_num only [Fintype.card_fin, Nat.factorial, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one, pow_succ, pow_zero] at h
    exact h
  have hproduct : g.pullbackVolumeDensity (cylinderNeckChart N q s) x *
      |A.symm.toContinuousLinearMap.det| = 1 := by
    have h := congrArg (fun t : ℝ => |t|) A.toLinearEquiv.det_mul_det_symm
    change |A.toContinuousLinearMap.det * A.symm.toContinuousLinearMap.det| = |1| at h
    simpa only [abs_mul, abs_one, hdet] using h
  have hnonneg : 0 ≤ g.pullbackVolumeDensity (cylinderNeckChart N q s) x := by
    rw [← hdet]
    exact abs_nonneg _
  constructor
  · have h := mul_le_mul_of_nonneg_left hinvdet hnonneg
    rw [hproduct] at h
    linarith
  · have h := g.pullbackVolumeDensity_le_of_differential_bound hi
      (fun v => (hspeed v).2)
    norm_num at h ⊢
    exact h

end PoincareConjecture.M28
