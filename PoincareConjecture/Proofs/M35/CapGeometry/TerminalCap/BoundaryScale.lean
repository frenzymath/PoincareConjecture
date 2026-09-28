import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.OriginalComparison
import PoincareConjecture.Proofs.M35.CapGeometry.RadialCoreScalarWitness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)

theorem radialArclength_intrinsic_center (q : UnitTwoSphere) {a : ℝ}
    (ha : 0 ≤ a) :
    radialArclength g ‖intrinsicSpatialInverse g hrotation hcomplete (a • q.val)‖ = a := by
  rw [intrinsicSpatialInverse_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
    norm_eq_of_mem_sphere, mul_one]
  exact (radialArclengthOrderIso g hrotation hcomplete).apply_symm_apply a

theorem radial_boundary_scalar_gt_quarter (P : M35StandardCapPredecessors)
    (D : LeviCivitaData g) (hsec : D.NonnegativeSectionalCurvature)
    (q : UnitTwoSphere) {a b Q epsilon : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hQ : 0 < Q) (he : 0 < epsilon)
    (hunit : Q * b ^ 2 = 1)
    (hradius : Q * intrinsicWarpingRadius g hrotation hcomplete a ^ 2 < 4)
    (hroom : 4 * b < a - b * epsilon⁻¹) :
    Q < 4 * D.scalarCurvature
      (intrinsicSpatialInverse g hrotation hcomplete ((a - b * epsilon⁻¹) • q.val)) := by
  let f := intrinsicWarpingRadius g hrotation hcomplete a
  let a' := a - b * epsilon⁻¹
  let y := intrinsicSpatialInverse g hrotation hcomplete (a' • q.val)
  have hf : 0 < f := intrinsicWarpingRadius_pos g hrotation hcomplete ha
  have hfb : f < 2 * b := by
    have hsq : f ^ 2 < 4 * b ^ 2 := by
      apply (mul_lt_mul_iff_of_pos_left hQ).mp
      nlinarith only [hradius, hunit]
    nlinarith only [hsq, hf, hb]
  have ha' : 0 < a' := (mul_pos (by norm_num) hb).trans hroom
  have hr : radialArclength g ‖y‖ = a' :=
    radialArclength_intrinsic_center g hrotation hcomplete q ha'.le
  have hw : 0 < b * epsilon⁻¹ := mul_pos hb (inv_pos.mpr he)
  have hs := radial_core_scalar_witness P g D hrotation hcomplete hsec ha y
    (by rw [hr]; change 2 * f ≤ a'; linarith only [hfb, hroom])
    (by rw [hr]; dsimp only [a']; linarith only [hw])
  have hR : 0 < D.scalarCurvature y := by
    by_contra hbad
    have hprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg f) (not_lt.mp hbad)
    change 1 ≤ f ^ 2 * D.scalarCurvature y at hs
    linarith only [hs, hprod]
  have hmul := mul_lt_mul_of_pos_right hradius hR
  have hscalar := mul_le_mul_of_nonneg_left hs hQ.le
  change Q < 4 * D.scalarCurvature y
  nlinarith only [hmul, hscalar]

theorem scalar_length_lt_twice {Q Q' b b' : ℝ}
    (hQ' : 0 < Q') (hb : 0 < b) (hb' : 0 < b')
    (hunit : Q * b ^ 2 = 1) (hunit' : Q' * b' ^ 2 = 1)
    (hscalar : Q < 4 * Q') : b' < 2 * b := by
  have h := mul_lt_mul_of_pos_right hscalar (sq_pos_of_pos hb)
  rw [hunit] at h
  have hsq : b' ^ 2 < 4 * b ^ 2 := by
    apply (mul_lt_mul_iff_of_pos_left hQ').mp
    nlinarith only [h, hunit']
  nlinarith only [hsq, hb', hb]

end PoincareConjecture.M35.Uniqueness
