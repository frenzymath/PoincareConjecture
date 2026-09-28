import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryProjectedPath
import PoincareConjecture.Proofs.M34.Standard.CompatibleCylinderCurve

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} {F : RicciFlow n M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)
  (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)

noncomputable def ordinaryLiftedCurve (T : ℝ) (gamma : ℝ → M) :
    ℝ → R.product.spacetime.Point := fun s =>
  R.product.productCylinder.toSpacetime
    ((R.product.timeIntervals.interval I).realParam (T - s), gamma s)

noncomputable def ordinaryLiftedHorizontal (T : ℝ) (gamma : ℝ → M) (s : ℝ) :
    R.product.spacetime.Horizontal (ordinaryLiftedCurve R T gamma s) :=
  R.product.productMetric.spatialTangentEquiv
    ((R.product.timeIntervals.interval I).realParam (T - s)) (gamma s)
    (curveVelocity gamma s)

theorem ordinaryLiftedCurve_integrand (T : ℝ) (gamma : ℝ → M) {s : ℝ}
    (hs : T - s ∈ I.domain) :
    M14RawLIntegrand (ordinaryProductLGeometry R hRicci)
      (ordinaryLiftedCurve R T gamma) (ordinaryLiftedHorizontal R T gamma) s =
      backwardLIntegrand F T gamma s := by
  let D := R.product.timeIntervals.interval I
  let t := D.realParam (T - s)
  have hscalar := ordinaryProduct_scalar_eq R F.connection t (gamma s)
  have hmetric := ordinaryProduct_inner_eq R.product t (gamma s)
    (curveVelocity gamma s) (curveVelocity gamma s)
  have htime : t.val = T - s := D.realParam_val hs
  rw [htime] at hscalar hmetric
  change Real.sqrt s * (horizontalScalarCurvature R.leafwiseConnection
      (R.product.productCylinder.toSpacetime (t, gamma s)) +
    R.product.spacetime.horizontalMetric.inner
      (R.product.productCylinder.toSpacetime (t, gamma s))
      (R.product.productMetric.spatialTangentEquiv t (gamma s) (curveVelocity gamma s))
      (R.product.productMetric.spatialTangentEquiv t (gamma s) (curveVelocity gamma s))) = _
  rw [← hscalar, ← hmetric]
  rfl

theorem ordinaryLiftedCurve_regular {T a b : ℝ} (q : BackwardTimePath F T a b) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) 1
      (ordinaryLiftedCurve R T q.curve) (Ioo a b) := by
  have hclock := realParam_backward_contMDiffOn (R.product.timeIntervals.interval I) T
    (fun s hs => q.time_mem s (Ioo_subset_Icc_self hs))
  exact (R.product.productCylinder.smooth.of_le (by simp)).comp_contMDiffOn
    ((hclock.of_le (by simp)).prodMk q.regular)

set_option backward.isDefEq.respectTransparency false in

theorem ordinaryLiftedCurve_derivative {T a b : ℝ} (q : BackwardTimePath F T a b)
    {s : ℝ} (hs : s ∈ Ioo a b) :
    mfderiv (𝓘(ℝ, ℝ)) (spacetimeModel n) (ordinaryLiftedCurve R T q.curve) s 1 =
      -R.product.spacetime.timeVector (ordinaryLiftedCurve R T q.curve s) +
        (ordinaryLiftedHorizontal R T q.curve s).val := by
  have hq := (q.regular.contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt
    (by norm_num)
  have hclock : HasDerivWithinAt (fun r => T - r) (-1) (Ioo a b) s := by
    simpa using ((hasDerivAt_id s).const_sub T).hasDerivWithinAt
  have hv := compatibleCylinder_curve_mfderivWithin_one R.product.productCylinder
    R.product.productMetric hs (isOpen_Ioo.uniqueDiffWithinAt hs) hclock
    (fun r hr => q.time_mem r (Ioo_subset_Icc_self hr)) hq.mdifferentiableWithinAt
  have hlift := (ordinaryLiftedCurve_regular R q).contMDiffAt
    (isOpen_Ioo.mem_nhds hs) |>.mdifferentiableAt (by norm_num)
  change MDifferentiableAt (𝓘(ℝ, ℝ)) (spacetimeModel n)
    (fun r => R.product.productCylinder.toSpacetime
      ((R.product.timeIntervals.interval I).realParam (T - r), q.curve r)) s at hlift
  rw [mfderivWithin_eq_mfderiv (isOpen_Ioo.uniqueMDiffWithinAt hs) hlift,
    mfderivWithin_eq_mfderiv (isOpen_Ioo.uniqueMDiffWithinAt hs) hq] at hv
  rw [neg_one_smul] at hv
  convert! hv using 1

noncomputable def ordinaryLiftedPath {T a b : ℝ} (q : BackwardTimePath F T a b) :
    M14BackwardPath (ordinaryProductLGeometry R hRicci) T a b
      (R.product.productCylinder.toSpacetime
        ((⟨T - a, q.time_mem a ⟨le_rfl, q.ordered.le⟩⟩, q.curve a)))
      (R.product.productCylinder.toSpacetime
        ((⟨T - b, q.time_mem b ⟨q.ordered.le, le_rfl⟩⟩, q.curve b))) where
  tau_nonneg := q.nonnegative
  tau_lt := q.ordered
  base_time := R.product.productCylinder.time_eq _
  endpoint_time := R.product.productCylinder.time_eq _
  curve := ordinaryLiftedCurve R T q.curve
  curve_start := by
    apply congrArg R.product.productCylinder.toSpacetime
    apply Prod.ext
    · exact Subtype.ext ((R.product.timeIntervals.interval I).realParam_val
        (q.time_mem a ⟨le_rfl, q.ordered.le⟩))
    · rfl
  curve_end := by
    apply congrArg R.product.productCylinder.toSpacetime
    apply Prod.ext
    · exact Subtype.ext ((R.product.timeIntervals.interval I).realParam_val
        (q.time_mem b ⟨q.ordered.le, le_rfl⟩))
    · rfl
  curve_time := by
    intro s hs
    exact (R.product.productCylinder.time_eq _).trans
      ((R.product.timeIntervals.interval I).realParam_val (q.time_mem s hs))
  curve_continuous := R.product.productCylinder.smooth.continuous.comp_continuousOn
    (((R.product.timeIntervals.interval I).realParam_continuousOn.comp
      (continuous_const.sub continuous_id).continuousOn q.time_mem).prodMk q.continuous)
  curve_regular := ordinaryLiftedCurve_regular R q
  horizontal_velocity := ordinaryLiftedHorizontal R T q.curve
  derivative_eq := fun s hs => ordinaryLiftedCurve_derivative R q hs
  action_integrable := q.l_integrable.congr_uIoo (by
    rw [uIoo_of_le q.ordered.le]
    intro s hs
    exact (ordinaryLiftedCurve_integrand R hRicci T q.curve
      (q.time_mem s (Ioo_subset_Icc_self hs))).symm)

end PoincareConjecture.M34
