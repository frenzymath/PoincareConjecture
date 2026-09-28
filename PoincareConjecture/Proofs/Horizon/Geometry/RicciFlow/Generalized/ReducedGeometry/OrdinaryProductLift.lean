import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.ReducedGeometry.OrdinaryProductPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology intervalIntegral
open Set Filter

universe u

namespace PoincareConjecture.OrdinaryProductRicciGeometry

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} (F : RicciFlow n M I.domain)
  (P : OrdinaryProductRicciGeometry F.metric I)
  {T τ₁ τ₂ : ℝ} (q : BackwardTimePath F T τ₁ τ₂)

def liftCurve (s : ℝ) : P.product.spacetime.Point :=
  P.product.productCylinder.toSpacetime
    ((P.product.timeIntervals.interval I).realParam (T - s), q.curve s)

@[simp] theorem pointMap_liftCurve (s : ℝ) :
    P.pointMap (P.liftCurve F q s) = q.curve s :=
  P.pointMap_productCylinder _ _

theorem liftCurve_time {s : ℝ} (hs : s ∈ Icc τ₁ τ₂) :
    P.product.spacetime.timeFunction (P.liftCurve F q s) = T - s := by
  rw [liftCurve, P.product.productCylinder.time_eq]
  exact (P.product.timeIntervals.interval I).realParam_val (q.time_mem s hs)

theorem liftCurve_continuous : ContinuousOn (P.liftCurve F q) (Icc τ₁ τ₂) := by
  apply P.product.productCylinder.smooth.continuous.comp_continuousOn
  exact ((P.product.timeIntervals.interval I).realParam_continuousOn.comp
    (continuous_const.sub continuous_id).continuousOn
    (fun s hs => q.time_mem s hs)).prodMk q.continuous

theorem liftCurve_regular :
    ContMDiffOn 𝓘(ℝ) (spacetimeModel n) 1 (P.liftCurve F q) (Ioo τ₁ τ₂) := by
  apply (P.product.productCylinder.smooth.of_le (by simp)).comp_contMDiffOn
  exact (((P.product.timeIntervals.interval I).realParam_smoothOn.of_le (by simp)).comp
    (contMDiff_const.sub contMDiff_id).contMDiffOn
    (fun s hs => q.time_mem s ⟨hs.1.le, hs.2.le⟩)).prodMk q.regular

def liftVelocity (s : ℝ) : P.product.spacetime.Horizontal (P.liftCurve F q s) :=
  P.product.spacetime.horizontalProjection (P.liftCurve F q s)
    (mfderiv 𝓘(ℝ) (spacetimeModel n) (P.liftCurve F q) s (1 : ℝ))

theorem liftCurve_derivative {s : ℝ} (hs : s ∈ Ioo τ₁ τ₂) :
    mfderiv 𝓘(ℝ) (spacetimeModel n) (P.liftCurve F q) s (1 : ℝ) =
      -P.product.spacetime.timeVector (P.liftCurve F q s) +
        (P.liftVelocity F q s).val := by
  have hd := ((P.liftCurve_regular F q).mdifferentiableOn (by simp) s hs).mdifferentiableAt
    (isOpen_Ioo.mem_nhds hs)
  have ht : HasDerivAt
      (P.product.spacetime.timeFunction ∘ P.liftCurve F q) (-1) s := by
    have ha : HasDerivAt (fun r : ℝ => T - r) (-1) s := by
      exact HasDerivAt.const_sub T (hasDerivAt_id s)
    apply ha.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    exact P.liftCurve_time F q ⟨hr.1.le, hr.2.le⟩
  have hts : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞
      P.product.spacetime.timeFunction := P.product.spacetime.time_smooth
  have hc := mfderiv_comp s
    (hts.mdifferentiable (by simp) (P.liftCurve F q s)) hd
  have hc1 := congrArg (fun L => L (1 : ℝ)) hc
  have hclock : mfderiv 𝓘(ℝ) 𝓘(ℝ)
      (P.product.spacetime.timeFunction ∘ P.liftCurve F q) s (1 : ℝ) = -1 := by
    rw [mfderiv_eq_fderiv]
    exact ht.deriv
  have htime : mfderiv (spacetimeModel n) 𝓘(ℝ)
      P.product.spacetime.timeFunction (P.liftCurve F q s)
      (mfderiv 𝓘(ℝ) (spacetimeModel n) (P.liftCurve F q) s (1 : ℝ)) = -1 :=
    hc1.symm.trans hclock
  have hsplit := P.product.spacetime.tangent_decomposition (P.liftCurve F q s)
    (mfderiv 𝓘(ℝ) (spacetimeModel n) (P.liftCurve F q) s (1 : ℝ))
  change mfderiv 𝓘(ℝ) (spacetimeModel n) (P.liftCurve F q) s (1 : ℝ) =
    (mfderiv (spacetimeModel n) 𝓘(ℝ) P.product.spacetime.timeFunction
      (P.liftCurve F q s)
      (mfderiv 𝓘(ℝ) (spacetimeModel n) (P.liftCurve F q) s (1 : ℝ))) •
      P.product.spacetime.timeVector (P.liftCurve F q s) +
      (P.liftVelocity F q s).val at hsplit
  erw [htime] at hsplit
  exact hsplit.trans (congrArg
    (fun v : TangentSpace (spacetimeModel n) (P.liftCurve F q s) =>
      v + (P.liftVelocity F q s).val)
    (neg_one_smul ℝ (P.product.spacetime.timeVector (P.liftCurve F q s))))

theorem liftVelocity_projection {s : ℝ} (hs : s ∈ Ioo τ₁ τ₂) :
    mfderiv (spacetimeModel n) (𝓡 n) P.pointMap (P.liftCurve F q s)
      (P.liftVelocity F q s).val = curveVelocity q.curve s := by
  have hd := ((P.liftCurve_regular F q).mdifferentiableOn (by simp) s hs).mdifferentiableAt
    (isOpen_Ioo.mem_nhds hs)
  have hc := mfderiv_comp s
    (P.pointMap_smooth.mdifferentiable (by simp) (P.liftCurve F q s)) hd
  have heq : P.pointMap ∘ P.liftCurve F q = q.curve := by
    funext r
    exact P.pointMap_liftCurve F q r
  rw [heq] at hc
  have hc1 := congrArg (fun L => L (1 : ℝ)) hc
  change curveVelocity q.curve s =
    mfderiv (spacetimeModel n) (𝓡 n) P.pointMap (P.liftCurve F q s)
      (mfderiv 𝓘(ℝ) (spacetimeModel n) (P.liftCurve F q) s (1 : ℝ)) at hc1
  erw [P.liftCurve_derivative F q hs,
    map_add, map_neg, P.pointMap_mfderiv_timeVector_at, neg_zero, zero_add] at hc1
  exact hc1.symm

theorem liftCurve_integrand
    (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)
    {s : ℝ} (hs : s ∈ Ioo τ₁ τ₂) :
    M14RawLIntegrand (P.toLGeometry h) (P.liftCurve F q) (P.liftVelocity F q) s =
      backwardLIntegrand F T q.curve s := by
  have ht := P.liftCurve_time F q ⟨hs.1.le, hs.2.le⟩
  unfold M14RawLIntegrand backwardLIntegrand
  change Real.sqrt s *
      (horizontalScalarCurvature P.leafwiseConnection (P.liftCurve F q s) +
        P.product.spacetime.horizontalMetric.inner (P.liftCurve F q s)
          (P.liftVelocity F q s) (P.liftVelocity F q s)) = _
  rw [P.horizontalScalarCurvature_eq F.connection, ← P.pointMap_horizontal_metric,
    P.liftVelocity_projection F q hs, ht, P.pointMap_liftCurve]

def liftBackwardPath (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection) :
    M14BackwardPath (P.toLGeometry h) T τ₁ τ₂
      (P.product.productCylinder.toSpacetime
        (⟨T - τ₁, q.time_mem τ₁ ⟨le_rfl, q.ordered.le⟩⟩, q.curve τ₁))
      (P.product.productCylinder.toSpacetime
        (⟨T - τ₂, q.time_mem τ₂ ⟨q.ordered.le, le_rfl⟩⟩, q.curve τ₂)) where
  tau_nonneg := q.nonnegative
  tau_lt := q.ordered
  base_time := P.product.productCylinder.time_eq _
  endpoint_time := P.product.productCylinder.time_eq _
  curve := P.liftCurve F q
  curve_start := by
    unfold liftCurve
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      exact (P.product.timeIntervals.interval I).realParam_val
        (q.time_mem τ₁ ⟨le_rfl, q.ordered.le⟩)
    · rfl
  curve_end := by
    unfold liftCurve
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      exact (P.product.timeIntervals.interval I).realParam_val
        (q.time_mem τ₂ ⟨q.ordered.le, le_rfl⟩)
    · rfl
  curve_time := fun _ hs => P.liftCurve_time F q hs
  curve_continuous := P.liftCurve_continuous F q
  curve_regular := P.liftCurve_regular F q
  horizontal_velocity := P.liftVelocity F q
  derivative_eq := fun _ hs => P.liftCurve_derivative F q hs
  action_integrable := q.l_integrable.congr_uIoo (by
    intro s hs
    exact (P.liftCurve_integrand F q h
      (by simpa only [Set.uIoo_of_le q.ordered.le] using hs)).symm)

end

end PoincareConjecture.OrdinaryProductRicciGeometry
