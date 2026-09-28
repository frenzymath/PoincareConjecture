import PoincareConjecture.Proofs.M28.Generalized.FullNeckVolumeCharts









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M28

open tube PoincareConjecture.Proofs.M28.NeckAnalysis

private abbrev E := EuclideanSpace ℝ (Fin 3)

private theorem ordinary_neck_coordinates_norm_sq (v : E) :
    ‖v‖ ^ 2 = ‖(cylinderScalarCoordinateEquiv v).1‖ ^ 2 +
      (cylinderScalarCoordinateEquiv v).2 ^ 2 := by
  simp [cylinderScalarCoordinateEquiv_apply, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  ring

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}




theorem ordinary_neck_chart_speed_lower (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : E}
    (hx : x ∈ cylinderNeckChartDomain N q s) (hxnorm : ‖x‖ ≤ 1) (v : E) :
    (N.scale / 2) * ‖v‖ ≤
      g.tangentNorm (cylinderNeckChart N q s x)
        (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x v) := by
  let a := (cylinderScalarCoordinates s x).1
  let z := cylinderSphereParametrization q (cylinderScalarCoordinates s x)
  let w : RoundCylinderCoordinates :=
    (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm a
      (cylinderScalarCoordinateEquiv v).1, (cylinderScalarCoordinateEquiv v).2)
  have ha : a = (cylinderScalarCoordinateEquiv x).1 := by
    simp [a, cylinderScalarCoordinates]
  have ha1 : ‖a‖ ≤ 1 := by
    rw [ha]
    have hnorm := ordinary_neck_coordinates_norm_sq x
    nlinarith [norm_nonneg (cylinderScalarCoordinateEquiv x).1, norm_nonneg x,
      sq_nonneg (cylinderScalarCoordinateEquiv x).2]
  have hfactor : (1 / 2 : ℝ) ≤ sphereChartConformalFactor a := by
    have ha2 : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
    unfold sphereChartConformalFactor
    apply (le_div_iff₀ (by positivity : 0 < (‖a‖ ^ 2 + 4) ^ 2)).mpr
    nlinarith [sq_nonneg (‖a‖ ^ 2), sq_nonneg (1 - ‖a‖ ^ 2)]
  have hform : RoundCylinderMetric z w w =
      2 * sphereChartConformalFactor a * ‖(cylinderScalarCoordinateEquiv v).1‖ ^ 2 +
        (cylinderScalarCoordinateEquiv v).2 ^ 2 := by
    dsimp only [RoundCylinderMetric, EvolvingRoundCylinderMetric, z, w,
      cylinderSphereParametrization]
    rw [sphere_chart_inverse_inner_at, real_inner_self_eq_norm_sq]
    ring
  have hquadratic : ‖v‖ ^ 2 ≤ RoundCylinderMetric z w w := by
    rw [hform]
    have hl := mul_le_mul_of_nonneg_right hfactor
      (sq_nonneg ‖(cylinderScalarCoordinateEquiv v).1‖)
    have hn := ordinary_neck_coordinates_norm_sq v
    nlinarith only [hl, hn]
  have hsqrt : ‖v‖ ≤ Real.sqrt (RoundCylinderMetric z w w) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt ((sq_nonneg ‖v‖).trans hquadratic)]
    exact hquadratic
  rw [cylinderNeckChart_mfderiv_apply N q s hx]
  exact (mul_le_mul_of_nonneg_left hsqrt (div_nonneg N.scale_pos.le (by norm_num))).trans
    (N.coordinate_speed_bounds z hx.2 w).1




theorem ordinary_neck_chart_density_lower (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : E}
    (hx : x ∈ cylinderNeckChartDomain N q s) (hxnorm : ‖x‖ ≤ 1) :
    N.scale ^ 3 / 48 ≤ g.pullbackVolumeDensity (cylinderNeckChart N q s) x := by
  classical
  have hi := (cylinderNeckChart_mfderiv_isInvertible N q s hx).bijective.1
  obtain ⟨A, hA, hdet⟩ := g.exists_frozenPullbackEquiv hi
  have hinv (v : E) : ‖A.symm v‖ ≤ (2 / N.scale) * ‖v‖ := by
    have h := ordinary_neck_chart_speed_lower N q s hx hxnorm (A.symm v)
    rw [← hA, A.apply_symm_apply] at h
    calc
      ‖A.symm v‖ ≤ (2 * ‖v‖) / N.scale :=
        (le_div_iff₀ N.scale_pos).mpr (by linarith)
      _ = (2 / N.scale) * ‖v‖ := by ring
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hentry (i j : Fin 3) :
      |LinearMap.toMatrix b.toBasis b.toBasis
        A.symm.toContinuousLinearMap.toLinearMap i j| ≤ 2 / N.scale := by
    rw [LinearMap.toMatrix_apply]
    change |(A.symm (b j)) i| ≤ 2 / N.scale
    calc
      |(A.symm (b j)) i| ≤ ‖A.symm (b j)‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A.symm (b j)) i
      _ ≤ (2 / N.scale) * ‖b j‖ := hinv _
      _ = 2 / N.scale := by simp [b, EuclideanSpace.basisFun_apply]
  have hinvdet : |A.symm.toContinuousLinearMap.det| ≤ 48 / N.scale ^ 3 := by
    have h := Matrix.det_le (abv := AbsoluteValue.abs) hentry
    rw [LinearMap.det_toMatrix] at h
    norm_num only [Fintype.card_fin, Nat.factorial, nsmul_eq_mul,
      Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one] at h
    calc
      |A.symm.toContinuousLinearMap.det| ≤ 6 * (2 / N.scale) ^ 3 := h
      _ = 48 / N.scale ^ 3 := by ring
  have hproduct : g.pullbackVolumeDensity (cylinderNeckChart N q s) x *
      |A.symm.toContinuousLinearMap.det| = 1 := by
    have h := congrArg (fun t : ℝ => |t|) A.toLinearEquiv.det_mul_det_symm
    change |A.toContinuousLinearMap.det * A.symm.toContinuousLinearMap.det| = |1| at h
    simpa only [abs_mul, abs_one, hdet] using h
  have hnonneg : 0 ≤ g.pullbackVolumeDensity (cylinderNeckChart N q s) x := by
    rw [← hdet]
    exact abs_nonneg _
  have h := mul_le_mul_of_nonneg_left
    ((le_div_iff₀ (pow_pos N.scale_pos 3)).mp hinvdet) hnonneg
  rw [← mul_assoc, hproduct, one_mul] at h
  linarith

end PoincareConjecture.M28
