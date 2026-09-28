import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckTransfer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderMetricBounds
import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.AffineReadout











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M28.NeckTransfer

open PoincareConjecture.M28.tube

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X} {eta : ℝ}




theorem NeckGeometryCore.frozen_difference_germ (V : NeckGeometryCore g eta)
    (N : EpsilonNeck h) (Q : ℝ) (hQ : 0 < Q)
    (hscale : Q * N.scale ^ 2 = V.scale ^ 2)
    (q : UnitTwoSphere) {s : ℝ}
    (hsV : s ∈ Ioo (-eta⁻¹) eta⁻¹)
    (hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a b : Fin 3) :
    (fun p => roundCylinderTensorCoefficient V.tensor
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b -
      roundCylinderTensorCoefficient
        (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback h N.coordinate_map z v w)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) =ᶠ[𝓝 (0, s)]
      (fun p => V.scale⁻¹ ^ 2 *
        (g.pullbackCoefficients
            (V.coordinate_map ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s))
            (cylinderScalarCoordinateEquiv.symm (p - (0, s))) -
          RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric h Q hQ)
            (cylinderNeckChart N q s) (cylinderScalarCoordinateEquiv.symm (p - (0, s))))
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) := by
  have hV := cylinderMapCoefficients_inverse_frozen_germ (g := g)
    V.coordinate_map_smooth (V.scale⁻¹ ^ 2) q hsV a b
  have hN := cylinderMapCoefficients_inverse_frozen_germ (g := h)
    N.coordinate_map_smooth (N.scale⁻¹ ^ 2) q hsN a b
  have hcancel : V.scale⁻¹ ^ 2 * V.scale ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ V.scale_pos.ne', one_pow]
  have hnormal : V.scale⁻¹ ^ 2 * Q = N.scale⁻¹ ^ 2 := by
    apply (mul_left_inj' (pow_ne_zero 2 N.scale_pos.ne')).mp
    calc
      (V.scale⁻¹ ^ 2 * Q) * N.scale ^ 2 =
          V.scale⁻¹ ^ 2 * (Q * N.scale ^ 2) := by ring
      _ = 1 := by rw [hscale, hcancel]
      _ = N.scale⁻¹ ^ 2 * N.scale ^ 2 := by
        rw [← mul_pow, inv_mul_cancel₀ N.scale_pos.ne', one_pow]
  filter_upwards [hV, hN] with p hpV hpN
  refine (congrArg₂ (fun x y : ℝ => x - y) hpV hpN).trans ?_
  let x := cylinderScalarCoordinateEquiv.symm (p - (0, s))
  let v := EuclideanSpace.basisFun (Fin 3) ℝ a
  let w := EuclideanSpace.basisFun (Fin 3) ℝ b
  change V.scale⁻¹ ^ 2 * g.pullbackCoefficients
      (V.coordinate_map ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x v w -
    N.scale⁻¹ ^ 2 * h.pullbackCoefficients (cylinderNeckChart N q s) x v w =
      V.scale⁻¹ ^ 2 * (g.pullbackCoefficients
        (V.coordinate_map ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x v w -
      Q * h.pullbackCoefficients (cylinderNeckChart N q s) x v w)
  rw [mul_sub, ← mul_assoc, hnormal]





theorem NeckGeometryCore.norm_frozen_difference_jet_le (V : NeckGeometryCore g eta)
    (N : EpsilonNeck h) (Q : ℝ) (hQ : 0 < Q)
    (hscale : Q * N.scale ^ 2 = V.scale ^ 2)
    (q : UnitTwoSphere) {s : ℝ}
    (hsV : s ∈ Ioo (-eta⁻¹) eta⁻¹)
    (hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a b : Fin 3) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun p => roundCylinderTensorCoefficient V.tensor
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b -
      roundCylinderTensorCoefficient
        (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback h N.coordinate_map z v w)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) (0, s)‖ ≤
      V.scale⁻¹ ^ 2 * ‖cylinderScalarCoordinateEquiv.symm.toContinuousLinearMap‖ ^ m *
        ‖iteratedFDeriv ℝ m (fun x => g.pullbackCoefficients
            (V.coordinate_map ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x -
          RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric h Q hQ)
            (cylinderNeckChart N q s) x) 0‖ := by
  let P := fun x => g.pullbackCoefficients
    (V.coordinate_map ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x -
      RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric h Q hQ)
        (cylinderNeckChart N q s) x
  have hxV : cylinderScalarCoordinates s 0 ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ Ioo (-eta⁻¹) eta⁻¹ := by
    rw [cylinderScalarCoordinates_zero]
    refine ⟨?_, hsV⟩
    rw [← NeckAnalysis.sphere_chart_center q]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) q).map_source (mem_chart_source _ q)
  have hVP := g.contDiffAt_pullbackCoefficients
    (contMDiffAt_cylinderMap V.coordinate_map_smooth q s hxV)
  have hNP := RiemannianMetric.contDiffAt_pullbackCoefficients
    (M13.scaleSmoothMetric h Q hQ)
    ((contMDiffOn_cylinderNeckChart N q s).contMDiffAt
      ((isOpen_cylinderNeckChartDomain N q s).mem_nhds
        (zero_mem_cylinderNeckChartDomain N q hsN)))
  have hP : ContDiffAt ℝ ∞ P 0 := hVP.sub hNP
  rw [((V.frozen_difference_germ N Q hQ hscale q hsV hsN a b).iteratedFDeriv ℝ m).eq_of_nhds]
  have h := cylinderScalarCoordinateEquiv.symm.norm_iteratedFDeriv_affine_bilinear_smul_le
    (f := P) (0, s) (0, s) m
    (by simpa only [sub_self, map_zero] using
      hP.of_le (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞))
    (V.scale⁻¹ ^ 2) (EuclideanSpace.basisFun (Fin 3) ℝ a)
    (EuclideanSpace.basisFun (Fin 3) ℝ b)
  have ha := (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one a
  have hb := (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.norm_eq_one b
  simpa only [smul_eq_mul, sub_self, map_zero, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (V.scale⁻¹)), ha, hb, mul_one] using h

end PoincareConjecture.Proofs.M28.NeckTransfer
