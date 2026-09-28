import PoincareConjecture.Statements.M12GeneralizedEquation
import PoincareConjecture.Statements.M14GeneralizedLGeometry
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Interval.RealTime
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.CurvatureTransport











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} {g : ℝ → RiemannianMetric n M}



noncomputable def ordinaryProductLGeometry (R : OrdinaryProductRicciGeometry g I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection) :
    GeneralizedLGeometryTransport n (I.domain × M) (fun p => p.1.val) I where
  spacetime := R.product.spacetime
  slices := R.product.slices
  timeIntervals := R.product.timeIntervals
  gaugeCover := R.cover
  leafwise := R.leafwiseConnection
  ricciEquation := hRicci



noncomputable def ordinaryProductProjection (R : OrdinaryProductSpacetimeConclusion g I) :
    R.spacetime.Point → M := fun z => (R.productIdentification.symm z).2



theorem ordinaryProductProjection_eq (R : OrdinaryProductSpacetimeConclusion g I)
    (z : R.spacetime.Point) : ordinaryProductProjection R z = z.2 := by
  have h := R.productIdentification.apply_symm_apply z
  rw [R.productIdentification_eq] at h
  exact congrArg Prod.snd h



theorem ordinaryProductProjection_cylinder (R : OrdinaryProductSpacetimeConclusion g I)
    (t : (R.timeIntervals.interval I).Point) (x : M) :
    ordinaryProductProjection R (R.productCylinder.toSpacetime (t, x)) = x := by
  rw [ordinaryProductProjection_eq, R.productCylinder_eq]



theorem ordinaryProductProjection_contMDiff (R : OrdinaryProductSpacetimeConclusion g I) :
    ContMDiff (spacetimeModel n) (𝓡 n) ∞ (ordinaryProductProjection R) :=
  contMDiff_snd.comp R.productIdentification.symm.contMDiff



theorem ordinaryProductCylinder_range (R : OrdinaryProductSpacetimeConclusion g I) :
    range R.productCylinder.toSpacetime = univ := by
  apply eq_univ_of_forall
  intro z
  exact ⟨z, R.productCylinder_eq z⟩

set_option backward.isDefEq.respectTransparency false in


theorem ordinaryProductProjection_timeVector (R : OrdinaryProductSpacetimeConclusion g I)
    (t : (R.timeIntervals.interval I).Point) (x : M) :
    mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R)
      (R.productCylinder.toSpacetime (t, x))
      (R.spacetime.timeVector (R.productCylinder.toSpacetime (t, x))) = 0 := by
  let e := R.productCylinder
  let line := fun s : (R.timeIntervals.interval I).Point => e.toSpacetime (s, x)
  have hline : ContMDiff (𝓡∂ 1) (spacetimeModel n) ∞ line :=
    e.smooth.comp (contMDiff_id.prodMk contMDiff_const)
  have hfun : ordinaryProductProjection R ∘ line = fun _ => x :=
    funext (fun s => ordinaryProductProjection_cylinder R s x)
  have hd := mfderiv_comp t
    (ordinaryProductProjection_contMDiff R |>.mdifferentiableAt (by simp))
    (hline.mdifferentiableAt (by simp))
  rw [hfun, mfderiv_const] at hd
  have hv := congrArg (fun L : EuclideanSpace ℝ (Fin 1) →L[ℝ]
    EuclideanSpace ℝ (Fin n) => L ((R.timeIntervals.interval I).positiveTangent t)) hd
  change 0 = mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R)
    (e.toSpacetime (t, x))
    (mfderiv (𝓡∂ 1) (spacetimeModel n) line t
      ((R.timeIntervals.interval I).positiveTangent t)) at hv
  rw [e.worldline_derivative t x] at hv
  exact hv.symm

set_option backward.isDefEq.respectTransparency false in


theorem ordinaryProductProjection_spatialTangent (R : OrdinaryProductSpacetimeConclusion g I)
    (t : (R.timeIntervals.interval I).Point) (x : M) (v : TangentSpace (𝓡 n) x) :
    mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R)
      (R.productCylinder.toSpacetime (t, x))
      (R.productMetric.spatialTangentEquiv t x v).val = v := by
  let e := R.productCylinder
  let slice := fun y : M => e.toSpacetime (t, y)
  have hslice : ContMDiff (𝓡 n) (spacetimeModel n) ∞ slice :=
    e.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have hfun : ordinaryProductProjection R ∘ slice = id :=
    funext (fun y => ordinaryProductProjection_cylinder R t y)
  have hd := mfderiv_comp x
    (ordinaryProductProjection_contMDiff R |>.mdifferentiableAt (by simp))
    (hslice.mdifferentiableAt (by simp))
  rw [hfun, mfderiv_id] at hd
  have hv := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
    EuclideanSpace ℝ (Fin n) => L v) hd
  rw [R.productMetric.spatialTangentEquiv_eq]
  exact hv.symm

set_option backward.isDefEq.respectTransparency false in


theorem ordinaryProductProjection_timeVector_at (R : OrdinaryProductSpacetimeConclusion g I)
    (z : R.spacetime.Point) :
    mfderiv (spacetimeModel n) (𝓡 n) (ordinaryProductProjection R) z
      (R.spacetime.timeVector z) = 0 := by
  have h := ordinaryProductProjection_timeVector R z.1 z.2
  rw [R.productCylinder_eq] at h
  exact h

end PoincareConjecture.M34
