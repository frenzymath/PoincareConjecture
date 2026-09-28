import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.CoreCoefficientReadout











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M28.NeckTransfer

open PoincareConjecture.M28.tube

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X} {eta : ℝ}





theorem NeckGeometryCore.norm_frozen_difference_jet_le_of_scale_error
    (V : NeckGeometryCore g eta) (N : EpsilonNeck h) (Q : ℝ) (hQ : 0 < Q)
    (q : UnitTwoSphere) {s : ℝ}
    (hsV : s ∈ Ioo (-eta⁻¹) eta⁻¹)
    (hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a b : Fin 3) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun p => roundCylinderTensorCoefficient V.tensor
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b -
      roundCylinderTensorCoefficient
        (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback h N.coordinate_map z v w)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) (0, s)‖ ≤
      V.scale⁻¹ ^ 2 * ‖cylinderScalarCoordinateEquiv.symm.toContinuousLinearMap‖ ^ m *
        (‖iteratedFDeriv ℝ m (fun x => g.pullbackCoefficients
            (V.coordinate_map ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s)) x -
          RiemannianMetric.pullbackCoefficients (M13.scaleSmoothMetric h Q hQ)
            (cylinderNeckChart N q s) x) 0‖ +
          ‖iteratedFDeriv ℝ m (fun x => (Q * N.scale ^ 2 - V.scale ^ 2) •
            cylinderNeckCoefficients N q s x) 0‖) := by
  let : AddMonoid (SpacetimeBounds.MetricCoefficient 3) :=
    (inferInstance : NormedAddCommGroup (SpacetimeBounds.MetricCoefficient 3)).toAddMonoid
  let Q0 := V.scale ^ 2 / N.scale ^ 2
  have hQ0 : 0 < Q0 := div_pos (sq_pos_of_pos V.scale_pos) (sq_pos_of_pos N.scale_pos)
  have hscale : Q0 * N.scale ^ 2 = V.scale ^ 2 :=
    div_mul_cancel₀ _ (pow_ne_zero 2 N.scale_pos.ne')
  let T := g.pullbackCoefficients
    (V.coordinate_map ∘ (cylinderSphereParametrization q ∘ cylinderScalarCoordinates s))
  let E := fun x => T x - RiemannianMetric.pullbackCoefficients
    (M13.scaleSmoothMetric h Q hQ) (cylinderNeckChart N q s) x
  let S := fun x => (Q * N.scale ^ 2 - V.scale ^ 2) • cylinderNeckCoefficients N q s x
  have heq : (fun x => T x - RiemannianMetric.pullbackCoefficients
      (M13.scaleSmoothMetric h Q0 hQ0) (cylinderNeckChart N q s) x) = E + S := by
    funext x
    change T x - RiemannianMetric.pullbackCoefficients
      (M13.scaleSmoothMetric h Q0 hQ0) (cylinderNeckChart N q s) x =
        (T x - RiemannianMetric.pullbackCoefficients
          (M13.scaleSmoothMetric h Q hQ) (cylinderNeckChart N q s) x) +
            (Q * N.scale ^ 2 - V.scale ^ 2) • cylinderNeckCoefficients N q s x
    rw [scaleSmoothMetric_cylinderNeckCoefficients,
      scaleSmoothMetric_cylinderNeckCoefficients, hscale]
    ext v w
    change T x v w - V.scale ^ 2 * cylinderNeckCoefficients N q s x v w =
      (T x v w - (Q * N.scale ^ 2) * cylinderNeckCoefficients N q s x v w) +
        (Q * N.scale ^ 2 - V.scale ^ 2) * cylinderNeckCoefficients N q s x v w
    ring
  have hxV : cylinderScalarCoordinates s 0 ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ Ioo (-eta⁻¹) eta⁻¹ := by
    rw [cylinderScalarCoordinates_zero]
    refine ⟨?_, hsV⟩
    rw [← NeckAnalysis.sphere_chart_center q]
    exact (chartAt (EuclideanSpace ℝ (Fin 2)) q).map_source (mem_chart_source _ q)
  have hT : ContDiffAt ℝ ∞ T 0 := g.contDiffAt_pullbackCoefficients
    (contMDiffAt_cylinderMap V.coordinate_map_smooth q s hxV)
  have hN := (contMDiffOn_cylinderNeckChart N q s).contMDiffAt
    ((isOpen_cylinderNeckChartDomain N q s).mem_nhds
      (zero_mem_cylinderNeckChartDomain N q hsN))
  have hE : ContDiffAt ℝ ∞ E 0 := hT.sub
    (RiemannianMetric.contDiffAt_pullbackCoefficients (M13.scaleSmoothMetric h Q hQ) hN)
  have hC : ContDiffAt ℝ ∞ (cylinderNeckCoefficients N q s) 0 :=
    (contDiffOn_cylinderNeckCoefficients N q s).contDiffAt
      ((isOpen_cylinderNeckChartDomain N q s).mem_nhds
        (zero_mem_cylinderNeckChartDomain N q hsN))
  have hS : ContDiffAt ℝ ∞ S 0 := hC.const_smul _
  have hnorm : ‖iteratedFDeriv ℝ m (fun x => T x - RiemannianMetric.pullbackCoefficients
      (M13.scaleSmoothMetric h Q0 hQ0) (cylinderNeckChart N q s) x) 0‖ ≤
        ‖iteratedFDeriv ℝ m E 0‖ + ‖iteratedFDeriv ℝ m S 0‖ := by
    rw [heq, iteratedFDeriv_add_apply
      (hE.of_le (by exact_mod_cast le_top)) (hS.of_le (by exact_mod_cast le_top))]
    exact norm_add_le _ _
  exact (V.norm_frozen_difference_jet_le N Q0 hQ0 hscale q hsV hsN a b m).trans
    (mul_le_mul_of_nonneg_left hnorm
      (mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) _)))

end PoincareConjecture.Proofs.M28.NeckTransfer
