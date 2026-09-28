import PoincareConjecture.Statements.M11GeneralizedFlow
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SectionTransport.TimeBracket
import PoincareConjecture.Proofs.M34.Mathlib.ModelTangentSection

set_option autoImplicit false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M34

noncomputable section

variable {n : ℕ} {I : SpacetimeInterval}
  {g : ℝ → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

def ordinaryProductHorizontalLift (R : OrdinaryProductSpacetimeConclusion g I)
    (z : R.spacetime.Point) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] R.spacetime.Horizontal z :=
  (R.spacetime.horizontalProjection z).comp
    ((mfderiv (spacetimeModel n) (spacetimeModel n) R.productIdentification
      (R.productIdentification.symm z)).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin n))))

set_option backward.isDefEq.respectTransparency false in

theorem ordinaryProductHorizontalLift_cylinder
    (R : OrdinaryProductSpacetimeConclusion g I)
    (t : (R.timeIntervals.interval I).Point) (x v : EuclideanSpace ℝ (Fin n)) :
    ordinaryProductHorizontalLift R (R.productCylinder.toSpacetime (t, x)) v =
      R.productMetric.spatialTangentEquiv t x v := by
  have heq : (R.productIdentification : _ → R.spacetime.Point) =
      R.productCylinder.toSpacetime := by
    funext p
    exact (R.productIdentification_eq p).trans (R.productCylinder_eq p).symm
  have hinv : R.productIdentification.symm (R.productCylinder.toSpacetime (t, x)) =
      (t, x) := by
    rw [← heq, R.productIdentification.symm_apply_apply]
  change R.spacetime.horizontalProjection (R.productCylinder.toSpacetime (t, x))
    (mfderiv (spacetimeModel n) (spacetimeModel n) R.productIdentification
      (R.productIdentification.symm (R.productCylinder.toSpacetime (t, x))) (0, v)) = _
  rw [hinv]
  rw [heq]
  have hd := movingGauge_mfderiv_spatial R.productCylinder.toMovingSpacetimeGauge
    R.productMetric.toMovingSpacetimeGaugeGeometry t x v
  change mfderiv (spacetimeModel n) (spacetimeModel n)
    R.productCylinder.toSpacetime (t, x) (0, v) =
      (R.productMetric.spatialTangentEquiv t x v).val at hd
  exact (congrArg (R.spacetime.horizontalProjection _) hd).trans
    (R.spacetime.horizontalProjection_identity _ _)

set_option backward.isDefEq.respectTransparency false in

theorem ordinaryProductHorizontalLift_contMDiff
    (R : OrdinaryProductSpacetimeConclusion g I)
    {E H A : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {IA : ModelWithCorners ℝ E H}
    [TopologicalSpace A] [ChartedSpace H A] [IsManifold IA ∞ A]
    {z : A → R.spacetime.Point} {a : A → EuclideanSpace ℝ (Fin n)}
    (hz : ContMDiff IA (spacetimeModel n) ∞ z) (ha : ContMDiff IA (𝓡 n) ∞ a) :
    ContMDiff IA ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun r => TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := R.spacetime.Horizontal) (z r) (ordinaryProductHorizontalLift R (z r) (a r))) := by
  have hq := R.productIdentification.symm.contMDiff.comp hz
  have ht := (Bundle.contMDiff_zeroSection (IB := 𝓡∂ 1)
    (F := EuclideanSpace ℝ (Fin 1)) (n := ∞) ℝ
    (TangentSpace (𝓡∂ 1) : (R.timeIntervals.interval I).Point → Type _)).comp hq.fst
  have hx := (contMDiff_modelTangentMk (𝓡 n) ∞).comp
    (hq.snd.prodMk ha)
  have hp := (contMDiff_equivTangentBundleProd_symm (I := 𝓡∂ 1)
    (M := (R.timeIntervals.interval I).Point) (I' := 𝓡 n)
    (M' := EuclideanSpace ℝ (Fin n))).comp (ht.prodMk hx)
  have hd := (R.productIdentification.contMDiff.contMDiff_tangentMap
    (m := ∞) (by simp)).comp hp
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun w : TangentBundle (spacetimeModel n) R.spacetime.Point =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := R.spacetime.Horizontal)
          w.proj (R.spacetime.horizontalProjection w.proj w.2)) :=
    R.spacetime.horizontalProjection_smooth
  have hh := hproj.comp hd
  convert! hh using 1
  funext r
  change TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := R.spacetime.Horizontal)
      (z r) (R.spacetime.horizontalProjection (z r)
        (mfderiv (spacetimeModel n) (spacetimeModel n) R.productIdentification
          (R.productIdentification.symm (z r)) (0, a r))) =
    TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := R.spacetime.Horizontal)
      (R.productIdentification (R.productIdentification.symm (z r)))
      (R.spacetime.horizontalProjection
        (R.productIdentification (R.productIdentification.symm (z r)))
        (mfderiv (spacetimeModel n) (spacetimeModel n) R.productIdentification
          (R.productIdentification.symm (z r)) (0, a r)))
  rw [R.productIdentification.apply_symm_apply]

theorem ordinaryProductHorizontalLift_contMDiffOn
    (R : OrdinaryProductSpacetimeConclusion g I)
    {E H A : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {IA : ModelWithCorners ℝ E H}
    [TopologicalSpace A] [ChartedSpace H A] [IsManifold IA ∞ A]
    {U : Set A} {z : A → R.spacetime.Point} {a : A → EuclideanSpace ℝ (Fin n)}
    (hz : ContMDiffOn IA (spacetimeModel n) ∞ z U)
    (ha : ContMDiffOn IA (𝓡 n) ∞ a U) :
    ContMDiffOn IA ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun r => TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := R.spacetime.Horizontal) (z r) (ordinaryProductHorizontalLift R (z r) (a r))) U := by
  have h := ordinaryProductHorizontalLift_contMDiff R
    (z := fun p : R.spacetime.Point × EuclideanSpace ℝ (Fin n) => p.1)
    (a := fun p => p.2) contMDiff_fst contMDiff_snd
  exact h.comp_contMDiffOn (hz.prodMk ha)

theorem ordinaryProductHorizontalLift_smooth (R : OrdinaryProductSpacetimeConclusion g I)
    (v : EuclideanSpace ℝ (Fin n)) :
    IsSmoothHorizontalSectionOn R.spacetime
      (fun z => ordinaryProductHorizontalLift R z v) univ :=
  (ordinaryProductHorizontalLift_contMDiff R contMDiff_id contMDiff_const).contMDiffOn

theorem ordinaryProductHorizontalLift_pullback (R : OrdinaryProductSpacetimeConclusion g I)
    (v : EuclideanSpace ℝ (Fin n)) (t : (R.timeIntervals.interval I).Point)
    (x : EuclideanSpace ℝ (Fin n)) :
    pullbackHorizontalSection R.productMetric.toMovingSpacetimeGaugeGeometry
      (fun z => ordinaryProductHorizontalLift R z v) t x = v := by
  change (R.productMetric.spatialTangentEquiv t x).symm
    (ordinaryProductHorizontalLift R (R.productCylinder.toSpacetime (t, x)) v) = v
  rw [ordinaryProductHorizontalLift_cylinder]
  exact (R.productMetric.spatialTangentEquiv t x).symm_apply_apply v

end

end PoincareConjecture.M34
