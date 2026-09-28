import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Interval.RealTime
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SectionTransport.TimeBracket










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Set Filter Bundle

universe u v w

namespace PoincareConjecture

theorem SmoothSpacetimeInterval.hasDerivWithinAt_realParam
    {K : SpacetimeInterval} (T : SmoothSpacetimeInterval K)
    {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : T.Point → E} (t : T.Point)
    (hf : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, E) f t) :
    HasDerivWithinAt (fun s => f (T.realParam s))
      (mfderiv (𝓡∂ 1) 𝓘(ℝ, E) f t (T.positiveTangent t)) K.domain t.val := by
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  have hp := T.realParam_smoothOn.mdifferentiableOn (by simp) t.val t.property
  have hf' : MDifferentiableAt (𝓡∂ 1) 𝓘(ℝ, E) f (T.realParam t.val) := by
    simpa only [T.realParam_coe] using hf
  have hd := hf'.comp_mdifferentiableWithinAt t.val hp
  have hc := mfderiv_comp_mfderivWithin t.val hf' hp
    (uniqueDiffWithinAt_of_spacetimeInterval K t).uniqueMDiffWithinAt
  have hc1 := congrArg (fun L : ℝ →L[ℝ] E => L 1) hc
  change mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) (f ∘ T.realParam) K.domain t.val 1 =
    mfderiv (𝓡∂ 1) 𝓘(ℝ, E) f (T.realParam t.val)
      (mfderivWithin 𝓘(ℝ) (𝓡∂ 1) T.realParam K.domain t.val 1) at hc1
  rw [T.realParam_mfderivWithin_one,
    T.realParam_coe, mfderivWithin_eq_fderivWithin] at hc1
  exact hd.differentiableWithinAt.hasFDerivWithinAt.hasDerivWithinAt.congr_deriv hc1

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]

theorem movingGauge_hasDerivWithinAt_comp
    (e : MovingSpacetimeGauge F T C) {f : F.Point → ℝ}
    (t : T.Point) (x : C)
    (hf : MDifferentiableAt (spacetimeModel n) 𝓘(ℝ) f (e.toSpacetime (t, x))) :
    HasDerivWithinAt (fun s => f (e.toSpacetime (T.realParam s, x)))
      (mvfderiv (spacetimeModel n) f (e.toSpacetime (t, x))
        (movingGaugeTimeVelocity e t x)) K.domain t.val := by
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1)
      (EuclideanSpace ℝ (Fin n))) F.Point := F.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ F.Point := F.isManifold
  have hi : MDifferentiableAt (𝓡∂ 1) (spacetimeModel n)
      (fun s : T.Point => (s, x)) t :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have he := e.smooth.mdifferentiableAt (x := (t, x)) (by simp)
  have hd := T.hasDerivWithinAt_realParam t (hf.comp t (he.comp t hi))
  apply hd.congr_deriv
  rw [mfderiv_comp_apply t hf (he.comp t hi), mfderiv_comp_apply t he hi]
  change mvfderiv (spacetimeModel n) f (e.toSpacetime (t, x))
      (mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
        (mfderiv (𝓡∂ 1) (spacetimeModel n) (fun s : T.Point => (s, x)) t
          (T.positiveTangent t))) = _
  congr 2
  change mfderiv (𝓡∂ 1) ((𝓡∂ 1).prod (𝓡 n))
    (fun s : T.Point => (id s, (fun _ : T.Point => x) s)) t
    (T.positiveTangent t) = (T.positiveTangent t, 0)
  rw [mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const]
  rw [mfderiv_id, mfderiv_const]
  rfl

theorem movingGauge_hasDerivWithinAt_pullbackSection
    (e : MovingSpacetimeGauge F T C) (G : MovingSpacetimeGaugeGeometry e)
    (V : HorizontalSection F) (O : Set F.Point) (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O) (t : T.Point) (x : C)
    (hp : e.toSpacetime (t, x) ∈ O) :
    HasDerivWithinAt
      (fun s => (show EuclideanSpace ℝ (Fin n) from
        pullbackHorizontalSection G V (T.realParam s) x))
      (show EuclideanSpace ℝ (Fin n) from movingGaugeSectionTimeDerivative G V t x)
      K.domain t.val := by
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  have hs := (movingGauge_pullbackHorizontalSection_smoothAt e G V O hO hV (t, x) hp).comp t
    (contMDiffAt_id.prodMk contMDiffAt_const)
  have hc := (Bundle.contMDiffAt_totalSpace.mp hs).2
  have hraw : ContMDiffAt (𝓡∂ 1) (𝓡 n) ∞
      (fun s : T.Point => (show EuclideanSpace ℝ (Fin n) from
        pullbackHorizontalSection G V s x)) t := by
    change ContMDiffAt (𝓡∂ 1) (𝓡 n) ∞
      (fun s => (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n)) x ⟨x, pullbackHorizontalSection G V s x⟩).2) t at hc
    have heq (w : TangentSpace (𝓡 n) x) :
        (trivializationAt (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n)) x ⟨x, w⟩).2 = w := by
      rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ _
        (mem_baseSet_trivializationAt _ _ x) w]
      rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source _ x),
        mfderiv_extChartAt_self]
      rfl
    simpa only [heq] using hc
  rw [movingGaugeSectionTimeDerivative_eq_model e G V O hO hV t x hp]
  exact T.hasDerivWithinAt_realParam t (hraw.mdifferentiableAt (by simp))

end PoincareConjecture
