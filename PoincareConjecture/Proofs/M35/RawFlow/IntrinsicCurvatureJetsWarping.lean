import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (D : LeviCivitaData g)



theorem intrinsicCurvatureJet_zero_eq {s : ℝ} (hs : 0 < s) :
    intrinsicCurvatureJet g hrotation hcomplete D 0 s =
      -deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete)) s /
        intrinsicWarpingRadius g hrotation hcomplete s := by
  let r := (radialArclengthOrderIso g hrotation hcomplete).symm s
  let e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1
  have hr : 0 < r := radialArclengthOrderIso_symm_pos g hrotation hcomplete hs
  have hcurv : intrinsicCurvatureJet g hrotation hcomplete D 0 s =
      radialMixedCurvatureFactor g r / axisRadialCoefficient g r := by
    change D.curvatureTensor (r • e 2)
      ((Real.sqrt (axisAngularCoefficient g r))⁻¹ • e 0)
      ((Real.sqrt (axisRadialCoefficient g r))⁻¹ • e 2)
      ((Real.sqrt (axisAngularCoefficient g r))⁻¹ • e 0)
      ((Real.sqrt (axisRadialCoefficient g r))⁻¹ • e 2) = _
    rw [D.curvatureTensor_smul_first, D.curvatureTensor_smul_second,
      D.curvatureTensor_smul_third, D.curvatureTensor_smul_last,
      (rotational_sectional_numerators_axis D hrotation hr).2.1]
    field_simp [(Real.sqrt_pos.mpr (axisAngularCoefficient_pos g r)).ne',
      (Real.sqrt_pos.mpr (axisRadialCoefficient_pos g r)).ne',
      (axisRadialCoefficient_pos g r).ne']
    rw [Real.sq_sqrt (axisAngularCoefficient_pos g r).le,
      Real.sq_sqrt (axisRadialCoefficient_pos g r).le]
    ring
  rw [hcurv, radialMixedCurvatureFactor_eq_warping g hr,
    (intrinsicWarpingRadius_deriv_hasDerivAt g hrotation hcomplete hs).deriv]
  rfl



theorem intrinsicWarpingRadius_second_eq_curvature {s : ℝ} (hs : 0 ≤ s) :
    deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete)) s =
      -(intrinsicCurvatureJet g hrotation hcomplete D 0 s *
        intrinsicWarpingRadius g hrotation hcomplete s) := by
  have hpos (r : ℝ) (hr : 0 < r) :
      deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete)) r =
        -(intrinsicCurvatureJet g hrotation hcomplete D 0 r *
          intrinsicWarpingRadius g hrotation hcomplete r) := by
    rw [intrinsicCurvatureJet_zero_eq g hrotation hcomplete D hr]
    field_simp [(intrinsicWarpingRadius_pos g hrotation hcomplete hr).ne']
  have hfs := intrinsicWarpingRadius_contDiff g hrotation hcomplete
  have hsecond := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hfs).2).2
  have heq : IsClosed {r : ℝ |
      deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete)) r =
        -(intrinsicCurvatureJet g hrotation hcomplete D 0 r *
          intrinsicWarpingRadius g hrotation hcomplete r)} :=
    isClosed_eq hsecond.continuous
      (((intrinsicCurvatureJet_contDiff g hrotation hcomplete D 0).continuous.mul
        hfs.continuous).neg)
  have hsubset : Ioi 0 ⊆ {r : ℝ |
      deriv (deriv (intrinsicWarpingRadius g hrotation hcomplete)) r =
        -(intrinsicCurvatureJet g hrotation hcomplete D 0 r *
          intrinsicWarpingRadius g hrotation hcomplete r)} := fun r hr => hpos r hr
  exact closure_minimal hsubset heq (by rwa [closure_Ioi])



theorem intrinsicCurvatureJet_iteratedDeriv_bound (m : ℕ) {C : ℝ}
    (hC : ∀ x : StandardCapSpace, D.curvatureDerivativeNorm m x ≤ C)
    {s : ℝ} (hs : 0 ≤ s) :
    |iteratedDeriv m (intrinsicCurvatureJet g hrotation hcomplete D 0) s| ≤ C := by
  have hpos (r : ℝ) (hr : 0 < r) :
      |iteratedDeriv m (intrinsicCurvatureJet g hrotation hcomplete D 0) r| ≤ C := by
    rw [iteratedDeriv_intrinsicCurvatureJet g hrotation hcomplete D m hr]
    exact (abs_intrinsicCurvatureJet_le g hrotation hcomplete D m r).trans (hC _)
  have hcont := (intrinsicCurvatureJet_contDiff g hrotation hcomplete D 0).continuous_iteratedDeriv
    m (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
  have hclosed : IsClosed {r : ℝ |
      |iteratedDeriv m (intrinsicCurvatureJet g hrotation hcomplete D 0) r| ≤ C} :=
    isClosed_le hcont.abs continuous_const
  exact closure_minimal (s := Ioi (0 : ℝ)) (fun r hr => hpos r hr)
    hclosed (by rwa [closure_Ioi])

end PoincareConjecture.M35.Uniqueness
