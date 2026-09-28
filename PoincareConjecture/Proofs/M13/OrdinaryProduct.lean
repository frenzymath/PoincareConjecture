import PoincareConjecture.Definitions.M13OrdinaryRescaling
import PoincareConjecture.Proofs.M13.IntervalTransport
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval} {g : ℝ → RiemannianMetric n M}

noncomputable def productHorizontalEquiv
    (P : OrdinaryProductSpacetimeConclusion g I) (p : P.spacetime.Point) :
    TangentSpace (𝓡 n) p.2 ≃L[ℝ] P.spacetime.Horizontal p :=
  (P.productMetric.spatialTangentEquiv p.1 p.2).trans
    (ContinuousLinearEquiv.ofEq
      (spacetimeHorizontal P.spacetime.timeFunction (P.productCylinder.toSpacetime p))
      (spacetimeHorizontal P.spacetime.timeFunction p)
      (congrArg (fun q : P.spacetime.Point ↦
        (show Submodule ℝ (SpacetimeModelVector n) from
          spacetimeHorizontal P.spacetime.timeFunction q)) (P.productCylinder_eq p)))

theorem productHorizontalEquiv_val
    (P : OrdinaryProductSpacetimeConclusion g I) (p : P.spacetime.Point)
    (v : TangentSpace (𝓡 n) p.2) :
    (productHorizontalEquiv P p v).val =
      mfderiv (spacetimeModel n) (spacetimeModel n) P.productIdentification p (0, v) := by
  let : ChartedSpace (EuclideanHalfSpace 1) I.domain := (P.timeIntervals.interval I).chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ I.domain := (P.timeIntervals.interval I).isManifold
  change (P.productMetric.spatialTangentEquiv p.1 p.2 v).val = _
  let j : M → (P.timeIntervals.interval I).Point × M := fun y ↦ (p.1, y)
  have hj : MDifferentiable (𝓡 n) (spacetimeModel n) j :=
    mdifferentiable_const.prodMk mdifferentiable_id
  have hfun : (fun y : M ↦ P.productCylinder.toSpacetime (p.1, y)) =
      P.productIdentification ∘ j := by
    funext y
    exact (P.productCylinder_eq _).trans (P.productIdentification_eq _).symm
  have heq := mfderiv_congr (I := 𝓡 n) (I' := spacetimeModel n) (x := p.2) hfun
  have hcomp := mfderiv_comp p.2 (P.productIdentification.mdifferentiable (by simp) _)
    (hj p.2)
  have hvalue := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      SpacetimeModelVector n ↦ L v) (heq.trans hcomp)
  change mfderiv (𝓡 n) (spacetimeModel n)
      (fun y : M ↦ P.productCylinder.toSpacetime (p.1, y)) p.2 v =
    mfderiv (spacetimeModel n) (spacetimeModel n) P.productIdentification p
      (mfderiv (𝓡 n) (spacetimeModel n) j p.2 v) at hvalue
  have hright : mfderiv (𝓡 n) (spacetimeModel n) j p.2 v = (0, v) := by
    rw [show mfderiv (𝓡 n) (spacetimeModel n) j p.2 =
      ContinuousLinearMap.inr ℝ (TangentSpace (𝓡∂ 1) p.1) (TangentSpace (𝓡 n) p.2) from
      mfderiv_prod_right]
    rfl
  rw [hright] at hvalue
  exact (P.productMetric.spatialTangentEquiv_eq p.1 p.2 v).trans hvalue

theorem productHorizontalEquiv_metric
    (P : OrdinaryProductSpacetimeConclusion g I) (p : P.spacetime.Point)
    (u v : TangentSpace (𝓡 n) p.2) :
    P.spacetime.horizontalMetric.inner p (productHorizontalEquiv P p u)
      (productHorizontalEquiv P p v) = (g p.1.val).inner p.2 u v := by
  have hmetric := P.productMetric.metric_eq p.1 p.2 u v
  rw [P.productMetric_eq] at hmetric
  have htransport (q : P.spacetime.Point) (hq : q = p)
      (e : TangentSpace (𝓡 n) p.2 ≃L[ℝ] P.spacetime.Horizontal q) :
      P.spacetime.horizontalMetric.inner p
        (e.trans (ContinuousLinearEquiv.ofEq
          (spacetimeHorizontal P.spacetime.timeFunction q)
          (spacetimeHorizontal P.spacetime.timeFunction p)
          (congrArg (fun r : P.spacetime.Point ↦
            (show Submodule ℝ (SpacetimeModelVector n) from
              spacetimeHorizontal P.spacetime.timeFunction r)) hq)) u)
        (e.trans (ContinuousLinearEquiv.ofEq
          (spacetimeHorizontal P.spacetime.timeFunction q)
          (spacetimeHorizontal P.spacetime.timeFunction p)
          (congrArg (fun r : P.spacetime.Point ↦
            (show Submodule ℝ (SpacetimeModelVector n) from
              spacetimeHorizontal P.spacetime.timeFunction r)) hq)) v) =
      P.spacetime.horizontalMetric.inner q (e u) (e v) := by
    subst q
    rfl
  exact (htransport _ (P.productCylinder_eq p) _).trans hmetric.symm

noncomputable def ordinaryComparisonDiffeomorph
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (source : OrdinaryProductSpacetimeConclusion g I)
    {g' : ℝ → RiemannianMetric n M}
    (target : OrdinaryProductSpacetimeConclusion g' (parabolicInterval Q hQ a I)) :
    Diffeomorph (spacetimeModel n) (spacetimeModel n)
      target.spacetime.Point source.spacetime.Point ∞ :=
  target.productIdentification.symm.trans
    (((affineIntervalDiffeomorph I Q hQ a (source.timeIntervals.interval I)
      (target.timeIntervals.interval (parabolicInterval Q hQ a I))).symm.prodCongr
        (Diffeomorph.refl (𝓡 n) M ∞)).trans source.productIdentification)

theorem ordinaryComparisonDiffeomorph_coordinate
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (source : OrdinaryProductSpacetimeConclusion g I)
    {g' : ℝ → RiemannianMetric n M}
    (target : OrdinaryProductSpacetimeConclusion g' (parabolicInterval Q hQ a I))
    (p : (target.timeIntervals.interval (parabolicInterval Q hQ a I)).Point × M) :
    ordinaryComparisonDiffeomorph Q hQ a source target (target.productIdentification p) =
      source.productIdentification (ordinaryProductTimeMap Q hQ a I p) := by
  simp only [ordinaryComparisonDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    Diffeomorph.symm_apply_apply]
  rfl

theorem ordinaryComparisonDiffeomorph_eq
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (source : OrdinaryProductSpacetimeConclusion g I)
    {g' : ℝ → RiemannianMetric n M}
    (target : OrdinaryProductSpacetimeConclusion g' (parabolicInterval Q hQ a I))
    (p : target.spacetime.Point) :
    ordinaryComparisonDiffeomorph Q hQ a source target p =
      ordinaryProductTimeMap Q hQ a I p := by
  have h := ordinaryComparisonDiffeomorph_coordinate Q hQ a source target p
  simpa only [target.productIdentification_eq, source.productIdentification_eq] using h

theorem ordinaryComparisonDiffeomorph_derivative
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (source : OrdinaryProductSpacetimeConclusion g I)
    {g' : ℝ → RiemannianMetric n M}
    (target : OrdinaryProductSpacetimeConclusion g' (parabolicInterval Q hQ a I))
    (p : (target.timeIntervals.interval (parabolicInterval Q hQ a I)).Point × M)
    (b : ℝ) (v : TangentSpace (𝓡 n) p.2) :
    mfderiv (spacetimeModel n) (spacetimeModel n)
      (ordinaryComparisonDiffeomorph Q hQ a source target) (target.productIdentification p)
      (mfderiv (spacetimeModel n) (spacetimeModel n) target.productIdentification p
        (b • (target.timeIntervals.interval (parabolicInterval Q hQ a I)).positiveTangent p.1,
          v)) =
    mfderiv (spacetimeModel n) (spacetimeModel n) source.productIdentification
      (ordinaryProductTimeMap Q hQ a I p)
      ((b / Q) • (source.timeIntervals.interval I).positiveTangent
        (ordinaryProductTimeMap Q hQ a I p).1, v) := by
  let e := (affineIntervalDiffeomorph I Q hQ a (source.timeIntervals.interval I)
    (target.timeIntervals.interval (parabolicInterval Q hQ a I))).symm
  let d := e.prodCongr (Diffeomorph.refl (𝓡 n) M ∞)
  let f := ordinaryComparisonDiffeomorph Q hQ a source target
  have hd : mfderiv (spacetimeModel n) (spacetimeModel n) d p
      (b • (target.timeIntervals.interval (parabolicInterval Q hQ a I)).positiveTangent p.1,
        v) =
      ((b / Q) • (source.timeIntervals.interval I).positiveTangent (d p).1, v) := by
    rw [Diffeomorph.coe_prodCongr, mfderiv_prodMap
      (e.mdifferentiable (by simp) _) ((Diffeomorph.refl (𝓡 n) M ∞).mdifferentiable (by simp) _)]
    change (mfderiv (𝓡∂ 1) (𝓡∂ 1) e p.1
        (b • (target.timeIntervals.interval (parabolicInterval Q hQ a I)).positiveTangent p.1),
      mfderiv (𝓡 n) (𝓡 n) (Diffeomorph.refl (𝓡 n) M ∞) p.2 v) =
      ((b / Q) • (source.timeIntervals.interval I).positiveTangent (e p.1), v)
    have he : mfderiv (𝓡∂ 1) (𝓡∂ 1) e p.1
        ((target.timeIntervals.interval (parabolicInterval Q hQ a I)).positiveTangent p.1) =
        (1 / Q : ℝ) • (source.timeIntervals.interval I).positiveTangent (e p.1) :=
      affineIntervalDiffeomorph_inverse_derivative I Q hQ a _ _ p.1
    have hi : mfderiv (𝓡 n) (𝓡 n) (Diffeomorph.refl (𝓡 n) M ∞) p.2 v = v := by
      change mfderiv (𝓡 n) (𝓡 n) (@id M) p.2 v = v
      rw [mfderiv_id]
      rfl
    rw [map_smul, he, hi, smul_smul, mul_one_div]
  have hfun : f ∘ target.productIdentification = source.productIdentification ∘ d := by
    funext q
    exact ordinaryComparisonDiffeomorph_coordinate Q hQ a source target q
  have hdiff := mfderiv_congr (I := spacetimeModel n) (I' := spacetimeModel n)
    (x := p) hfun
  rw [mfderiv_comp _ (f.mdifferentiable (by simp) _)
      (target.productIdentification.mdifferentiable (by simp) _),
    mfderiv_comp _ (source.productIdentification.mdifferentiable (by simp) _)
      (d.mdifferentiable (by simp) _)] at hdiff
  have hvalue := congrArg (fun L : SpacetimeModelVector n →L[ℝ] SpacetimeModelVector n ↦
      L (b • (target.timeIntervals.interval (parabolicInterval Q hQ a I)).positiveTangent p.1,
        v)) hdiff
  change mfderiv (spacetimeModel n) (spacetimeModel n) f (target.productIdentification p)
      (mfderiv (spacetimeModel n) (spacetimeModel n) target.productIdentification p
        (b • (target.timeIntervals.interval (parabolicInterval Q hQ a I)).positiveTangent p.1,
          v)) =
    mfderiv (spacetimeModel n) (spacetimeModel n) source.productIdentification (d p)
      (mfderiv (spacetimeModel n) (spacetimeModel n) d p
        (b • (target.timeIntervals.interval (parabolicInterval Q hQ a I)).positiveTangent p.1,
          v)) at hvalue
  rw [hd] at hvalue
  exact hvalue

theorem ordinaryComparisonDiffeomorph_timeVector
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (source : OrdinaryProductSpacetimeConclusion g I)
    {g' : ℝ → RiemannianMetric n M}
    (target : OrdinaryProductSpacetimeConclusion g' (parabolicInterval Q hQ a I))
    (p : target.spacetime.Point) :
    mfderiv (spacetimeModel n) (spacetimeModel n)
      (ordinaryComparisonDiffeomorph Q hQ a source target) p (target.spacetime.timeVector p) =
      (1 / Q : ℝ) • source.spacetime.timeVector
        (ordinaryComparisonDiffeomorph Q hQ a source target p) := by
  have h := ordinaryComparisonDiffeomorph_derivative Q hQ a source target p 1 0
  have hs := congrArg (fun v ↦ (1 / Q : ℝ) • v)
    (source.product_timeVector (ordinaryProductTimeMap Q hQ a I p))
  rw [← map_smul] at hs
  change mfderiv (spacetimeModel n) (spacetimeModel n) source.productIdentification
      (ordinaryProductTimeMap Q hQ a I p)
      ((1 / Q : ℝ) • (source.timeIntervals.interval I).positiveTangent
        (ordinaryProductTimeMap Q hQ a I p).1,
        (1 / Q : ℝ) • (0 : TangentSpace (𝓡 n) p.2)) = _ at hs
  rw [smul_zero] at hs
  have hp := mfderiv_congr_point (I := spacetimeModel n) (I' := spacetimeModel n)
    (f := ordinaryComparisonDiffeomorph Q hQ a source target) (target.productIdentification_eq p)
  rw [hp] at h
  change @Eq (SpacetimeModelVector n) _ _ at h hs ⊢
  have hvalue := h.trans hs
  simp only [one_smul, target.product_timeVector] at hvalue

  let L : SpacetimeModelVector n →L[ℝ] SpacetimeModelVector n :=
    mfderiv (spacetimeModel n) (spacetimeModel n)
      (ordinaryComparisonDiffeomorph Q hQ a source target) p
  let χt : target.spacetime.Point → SpacetimeModelVector n := target.spacetime.timeVector
  let χs : source.spacetime.Point → SpacetimeModelVector n := source.spacetime.timeVector
  change L (χt (target.productIdentification p)) =
    (1 / Q : ℝ) • χs (source.productIdentification (ordinaryProductTimeMap Q hQ a I p)) at hvalue
  change L (χt p) = (1 / Q : ℝ) • χs (ordinaryComparisonDiffeomorph Q hQ a source target p)
  simpa only [target.productIdentification_eq, source.productIdentification_eq,
    ordinaryComparisonDiffeomorph_eq] using hvalue

noncomputable def ordinaryComparisonHorizontal
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (source : OrdinaryProductSpacetimeConclusion g I)
    {g' : ℝ → RiemannianMetric n M}
    (target : OrdinaryProductSpacetimeConclusion g' (parabolicInterval Q hQ a I))
    (p : target.spacetime.Point) :
    target.spacetime.Horizontal p ≃L[ℝ]
      source.spacetime.Horizontal (ordinaryComparisonDiffeomorph Q hQ a source target p) :=
  (productHorizontalEquiv target p).symm.trans
    (productHorizontalEquiv source (ordinaryComparisonDiffeomorph Q hQ a source target p))

theorem ordinaryComparisonHorizontal_val
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (source : OrdinaryProductSpacetimeConclusion g I)
    {g' : ℝ → RiemannianMetric n M}
    (target : OrdinaryProductSpacetimeConclusion g' (parabolicInterval Q hQ a I))
    (p : target.spacetime.Point) (v : target.spacetime.Horizontal p) :
    (ordinaryComparisonHorizontal Q hQ a source target p v).val =
      mfderiv (spacetimeModel n) (spacetimeModel n)
        (ordinaryComparisonDiffeomorph Q hQ a source target) p v.val := by
  let w := (productHorizontalEquiv target p).symm v
  have hv : v.val =
      mfderiv (spacetimeModel n) (spacetimeModel n) target.productIdentification p (0, w) := by
    rw [← productHorizontalEquiv_val]
    exact congrArg Subtype.val ((productHorizontalEquiv target p).apply_symm_apply v).symm
  change (productHorizontalEquiv source
    (ordinaryComparisonDiffeomorph Q hQ a source target p) w).val = _
  rw [productHorizontalEquiv_val, ordinaryComparisonDiffeomorph_eq, hv]
  have h := ordinaryComparisonDiffeomorph_derivative Q hQ a source target p 0 w
  have hp := mfderiv_congr_point (I := spacetimeModel n) (I' := spacetimeModel n)
    (f := ordinaryComparisonDiffeomorph Q hQ a source target) (target.productIdentification_eq p)
  rw [hp] at h
  change @Eq (SpacetimeModelVector n) _ _ at h ⊢
  simp only [zero_smul, zero_div] at h
  exact h.symm

theorem ordinaryParabolicProductComparison [Nonempty M]
    (F : RicciFlow n M I.domain) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (R : OrdinaryParabolicRescaling F Q hQ a)
    (source : OrdinaryProductRicciGeometry F.metric I)
    (target : OrdinaryProductRicciGeometry R.flow.metric (parabolicInterval Q hQ a I)) :
    Nonempty (OrdinaryParabolicProductComparison R source target) := by
  refine ⟨{
    source_equation := (source.equation_iff F.connection).2 F.equation
    target_equation := (target.equation_iff R.flow.connection).2 R.flow.equation
    comparison := ordinaryComparisonDiffeomorph Q hQ a source.product target.product
    comparison_eq := ordinaryComparisonDiffeomorph_eq Q hQ a source.product target.product
    coordinate_eq := ordinaryComparisonDiffeomorph_coordinate Q hQ a source.product target.product
    coordinate_derivative := ordinaryComparisonDiffeomorph_derivative Q hQ a
      source.product target.product
    time_vector_eq := ordinaryComparisonDiffeomorph_timeVector Q hQ a source.product target.product
    horizontalTangentEquiv := ordinaryComparisonHorizontal Q hQ a source.product target.product
    horizontalTangentEquiv_val := ordinaryComparisonHorizontal_val Q hQ a
      source.product target.product
    horizontal_metric := ?_ }⟩
  intro p u v
  let u' := (productHorizontalEquiv target.product p).symm u
  let v' := (productHorizontalEquiv target.product p).symm v
  change target.product.spacetime.horizontalMetric.inner p u v =
    Q * source.product.spacetime.horizontalMetric.inner
      (ordinaryComparisonDiffeomorph Q hQ a source.product target.product p)
      (productHorizontalEquiv source.product
        (ordinaryComparisonDiffeomorph Q hQ a source.product target.product p) u')
      (productHorizontalEquiv source.product
        (ordinaryComparisonDiffeomorph Q hQ a source.product target.product p) v')
  rw [productHorizontalEquiv_metric, ordinaryComparisonDiffeomorph_eq]
  have ht := productHorizontalEquiv_metric target.product p u' v'
  rw [(productHorizontalEquiv target.product p).apply_symm_apply,
    (productHorizontalEquiv target.product p).apply_symm_apply] at ht
  rw [ht]
  exact R.metric_eq p.1.val p.2 u' v'

end PoincareConjecture.M13
