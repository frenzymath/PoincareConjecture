import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Gauge.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.ReducedGeometry.OrdinaryCapture

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.OrdinaryProductRicciGeometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : ℝ → RiemannianMetric n M} {I : SpacetimeInterval}

def toLGeometry (P : OrdinaryProductRicciGeometry g I)
    (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection) :
    GeneralizedLGeometryTransport n (I.domain × M) (fun p => p.1.val) I where
  spacetime := P.product.spacetime
  slices := P.product.slices
  timeIntervals := P.product.timeIntervals
  gaugeCover := P.cover
  leafwise := P.leafwiseConnection
  ricciEquation := h

theorem intrinsicEquation_of_ricciFlow (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I) :
    IntrinsicGeneralizedRicciEquation P.leafwiseConnection :=
  (P.equation_iff F.connection).mpr F.equation

def ricciFlowLGeometry (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I) :
    GeneralizedLGeometryTransport n (I.domain × M) (fun p => p.1.val) I :=
  P.toLGeometry (P.intrinsicEquation_of_ricciFlow F)

variable (P : OrdinaryProductRicciGeometry g I)

theorem productCylinder_surjective : Function.Surjective P.product.productCylinder.toSpacetime :=
  fun p => ⟨p, P.product.productCylinder_eq p⟩

@[simp] theorem productCylinder_range : Set.range P.product.productCylinder.toSpacetime =
    Set.univ := Set.range_eq_univ.mpr P.productCylinder_surjective

def pointMap : P.product.spacetime.Point → M := fun p => p.2

@[simp] theorem pointMap_apply (p : P.product.spacetime.Point) :
    P.pointMap p = p.2 := rfl

@[simp] theorem pointMap_productCylinder
    (t : (P.product.timeIntervals.interval I).Point) (x : M) :
    P.pointMap (P.product.productCylinder.toSpacetime (t, x)) = x := by
  rw [P.product.productCylinder_eq]
  rfl

theorem pointMap_continuous : Continuous P.pointMap := continuous_snd

theorem pointMap_smooth : ContMDiff (spacetimeModel n) (𝓡 n) ∞ P.pointMap := by
  have h : P.pointMap = fun p => (P.product.productIdentification.symm p).2 := by
    funext p
    have he := P.product.productIdentification_eq (P.product.productIdentification.symm p)
    rw [P.product.productIdentification.apply_symm_apply] at he
    exact congrArg Prod.snd he
  rw [h]
  exact contMDiff_snd.comp P.product.productIdentification.symm.contMDiff

theorem productCylinder_pointMap
    (p : P.product.spacetime.Point) (t : ℝ)
    (ht : t ∈ I.domain) (hp : P.product.spacetime.timeFunction p = t) :
    P.product.productCylinder.toSpacetime (⟨t, ht⟩, P.pointMap p) = p := by
  rw [P.product.productCylinder_eq]
  apply Prod.ext
  · exact Subtype.ext hp.symm
  · rfl

theorem path_captured
    (h : IntrinsicGeneralizedRicciEquation P.leafwiseConnection)
    {T τ₁ τ₂ : ℝ} {x y : (P.toLGeometry h).Point}
    (p : M14BackwardPath (P.toLGeometry h) T τ₁ τ₂ x y) (s : ℝ) :
    p.curve s ∈ Set.range P.product.productCylinder.toSpacetime := by
  rw [P.productCylinder_range]
  trivial

end PoincareConjecture.OrdinaryProductRicciGeometry
