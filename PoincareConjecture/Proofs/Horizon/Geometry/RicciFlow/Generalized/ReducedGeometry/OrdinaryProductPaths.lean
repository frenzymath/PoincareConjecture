import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.ReducedGeometry.OrdinaryProduct
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Spacetime.Interval.RealTime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.OrdinaryProductRicciGeometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : ℝ → RiemannianMetric n M} {I : SpacetimeInterval}
  (P : OrdinaryProductRicciGeometry g I)

theorem pointMap_mfderiv_timeVector
    (t : (P.product.timeIntervals.interval I).Point) (x : M) :
    mfderiv (spacetimeModel n) (𝓡 n) P.pointMap
        (P.product.productCylinder.toSpacetime (t, x))
        (P.product.spacetime.timeVector
          (P.product.productCylinder.toSpacetime (t, x))) = 0 := by
  have hcomp := mfderiv_comp t
    (P.pointMap_smooth.mdifferentiable (by simp)
      (P.product.productCylinder.toSpacetime (t, x)))
    ((P.product.productCylinder.worldline_smooth x).mdifferentiable (by simp) t)
  have heq : P.pointMap ∘
      (fun s => P.product.productCylinder.toSpacetime (s, x)) = fun _ => x := by
    funext s
    exact P.pointMap_productCylinder s x
  rw [heq, mfderiv_const] at hcomp
  have hv := congrArg (fun L => L ((P.product.timeIntervals.interval I).positiveTangent t))
    hcomp
  change 0 = mfderiv (spacetimeModel n) (𝓡 n) P.pointMap
      (P.product.productCylinder.toSpacetime (t, x))
      (mfderiv (𝓡∂ 1) (spacetimeModel n)
        (fun s => P.product.productCylinder.toSpacetime (s, x)) t
        ((P.product.timeIntervals.interval I).positiveTangent t)) at hv
  rw [P.product.productCylinder.worldline_derivative] at hv
  exact hv.symm

theorem pointMap_mfderiv_spatial
    (t : (P.product.timeIntervals.interval I).Point) (x : M)
    (v : TangentSpace (𝓡 n) x) :
    mfderiv (spacetimeModel n) (𝓡 n) P.pointMap
        (P.product.productCylinder.toSpacetime (t, x))
        (P.product.productMetric.spatialTangentEquiv t x v).val = v := by
  have hs : ContMDiff (𝓡 n) (spacetimeModel n) ∞
      (fun y => P.product.productCylinder.toSpacetime (t, y)) :=
    P.product.productCylinder.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have hcomp := mfderiv_comp x
    (P.pointMap_smooth.mdifferentiable (by simp)
      (P.product.productCylinder.toSpacetime (t, x)))
    (hs.mdifferentiable (by simp) x)
  have heq : P.pointMap ∘
      (fun y => P.product.productCylinder.toSpacetime (t, y)) = id := by
    funext y
    exact P.pointMap_productCylinder t y
  rw [heq, mfderiv_id] at hcomp
  have hv := congrArg (fun L => L v) hcomp
  change v = mfderiv (spacetimeModel n) (𝓡 n) P.pointMap
      (P.product.productCylinder.toSpacetime (t, x))
      (mfderiv (𝓡 n) (spacetimeModel n)
        (fun y => P.product.productCylinder.toSpacetime (t, y)) x v) at hv
  rw [← P.product.productMetric.spatialTangentEquiv_eq] at hv
  exact hv.symm

theorem pointMap_mfderiv_timeVector_at (p : P.product.spacetime.Point) :
    mfderiv (spacetimeModel n) (𝓡 n) P.pointMap p
      (P.product.spacetime.timeVector p) = 0 := by
  obtain ⟨⟨t, x⟩, rfl⟩ := P.productCylinder_surjective p
  exact P.pointMap_mfderiv_timeVector t x

theorem pointMap_horizontal_metric (p : P.product.spacetime.Point)
    (v w : P.product.spacetime.Horizontal p) :
    (g (P.product.spacetime.timeFunction p)).inner (P.pointMap p)
        (mfderiv (spacetimeModel n) (𝓡 n) P.pointMap p v.val)
        (mfderiv (spacetimeModel n) (𝓡 n) P.pointMap p w.val) =
      P.product.spacetime.horizontalMetric.inner p v w := by
  obtain ⟨⟨t, x⟩, rfl⟩ := P.productCylinder_surjective p
  obtain ⟨v, rfl⟩ := (P.product.productMetric.spatialTangentEquiv t x).surjective v
  obtain ⟨w, rfl⟩ := (P.product.productMetric.spatialTangentEquiv t x).surjective w
  erw [P.product.productCylinder.time_eq, P.pointMap_productCylinder,
    P.pointMap_mfderiv_spatial, P.pointMap_mfderiv_spatial]
  simpa only [P.product.productMetric_eq] using P.product.productMetric.metric_eq t x v w

theorem horizontalScalarCurvature_eq (c : MetricLeviCivitaFamily g)
    (p : P.product.spacetime.Point) :
    horizontalScalarCurvature P.leafwiseConnection p =
      (c (P.product.spacetime.timeFunction p)).scalarCurvature (P.pointMap p) := by
  obtain ⟨t, x⟩ := p
  have hs := (c t.val).scalarCurvature_eq_of_local_isometry
    (P.leafwiseConnection.sliceConnection t.val) isOpen_univ
    (P.product.sliceIdentification t).contMDiff.contMDiffOn
    (fun y _ u v => (P.product.sliceMetric_eq t y u v).symm) (Set.mem_univ x)
  have heq : P.product.sliceIdentification t x =
      (⟨(t, x), rfl⟩ : (P.product.slices t.val).Point) := by
    apply Subtype.ext
    exact P.product.sliceIdentification_eq t x
  rw [heq] at hs
  exact hs.symm

theorem pointMap_path_velocity
    (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)
    {T τ₁ τ₂ : ℝ} {x y : (P.toLGeometry h).Point}
    (p : M14BackwardPath (P.toLGeometry h) T τ₁ τ₂ x y)
    {s : ℝ} (hs : s ∈ Set.Ioo τ₁ τ₂) :
    curveVelocity (P.pointMap ∘ p.curve) s =
      mfderiv (spacetimeModel n) (𝓡 n) P.pointMap (p.curve s)
        (p.horizontal_velocity s).val := by
  have hd := (p.curve_regular.mdifferentiableOn (by simp) s hs).mdifferentiableAt
    (isOpen_Ioo.mem_nhds hs)
  have hc := mfderiv_comp s
    (P.pointMap_smooth.mdifferentiable (by simp) (p.curve s)) hd
  unfold curveVelocity
  rw [hc]
  change mfderiv (spacetimeModel n) (𝓡 n) P.pointMap (p.curve s)
      (mfderiv 𝓘(ℝ) (spacetimeModel n) p.curve s (1 : ℝ)) = _
  erw [p.derivative_eq s hs,
    map_add, map_neg, P.pointMap_mfderiv_timeVector_at, neg_zero, zero_add]

theorem backwardLIntegrand_pointMap
    (F : RicciFlow n M I.domain) (P : OrdinaryProductRicciGeometry F.metric I)
    (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)
    {T τ₁ τ₂ : ℝ} {x y : (P.toLGeometry h).Point}
    (p : M14BackwardPath (P.toLGeometry h) T τ₁ τ₂ x y)
    {s : ℝ} (hs : s ∈ Set.Ioo τ₁ τ₂) :
    backwardLIntegrand F T (P.pointMap ∘ p.curve) s =
      M14RawLIntegrand (P.toLGeometry h) p.curve p.horizontal_velocity s := by
  have ht : P.product.spacetime.timeFunction (p.curve s) = T - s :=
    p.curve_time s ⟨hs.1.le, hs.2.le⟩
  unfold backwardLIntegrand M14RawLIntegrand
  erw [P.pointMap_path_velocity h p hs, ← ht,
    P.pointMap_horizontal_metric, ← P.horizontalScalarCurvature_eq F.connection]
  rfl

noncomputable def projectBackwardPath
    (F : RicciFlow n M I.domain) (P : OrdinaryProductRicciGeometry F.metric I)
    (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)
    {T τ₁ τ₂ : ℝ} (hT : T ∈ I.domain) {x y : (P.toLGeometry h).Point}
    (p : M14BackwardPath (P.toLGeometry h) T τ₁ τ₂ x y) :
    BackwardTimePath F T τ₁ τ₂ where
  curve := P.pointMap ∘ p.curve
  nonnegative := p.tau_nonneg
  ordered := p.tau_lt
  terminal_mem := hT
  time_mem := by
    intro s hs
    rw [← p.curve_time s hs]
    exact (p.curve s).1.property
  continuous := P.pointMap_continuous.comp_continuousOn p.curve_continuous
  regular := P.pointMap_smooth.of_le (by simp) |>.comp_contMDiffOn p.curve_regular
  l_integrable := p.action_integrable.congr_uIoo (by
    intro s hs
    exact (P.backwardLIntegrand_pointMap F h p
      (by simpa only [Set.uIoo_of_le p.tau_lt.le] using hs)).symm)

@[simp] theorem projectBackwardPath_curve
    (F : RicciFlow n M I.domain) (P : OrdinaryProductRicciGeometry F.metric I)
    (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)
    {T τ₁ τ₂ : ℝ} (hT : T ∈ I.domain) {x y : (P.toLGeometry h).Point}
    (p : M14BackwardPath (P.toLGeometry h) T τ₁ τ₂ x y) :
    (P.projectBackwardPath F h hT p).curve = P.pointMap ∘ p.curve := rfl

end PoincareConjecture.OrdinaryProductRicciGeometry
