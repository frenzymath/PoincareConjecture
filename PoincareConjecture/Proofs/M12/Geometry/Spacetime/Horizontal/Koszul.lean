import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Connection
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SectionTransport
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.Connections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u v

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ t : ℝ, SpacetimeSliceGeometry F t}

section Gauge

variable {K : SpacetimeInterval} {T : SmoothSpacetimeInterval K}
  {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge F T C}

private theorem horizontalBracket_pullback
    (G : MovingSpacetimeGaugeGeometry e)
    {V W : HorizontalSection F} {O : Set F.Point} (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O)
    (hW : IsSmoothHorizontalSectionOn F W O)
    (t : T.Point) (x : C) (hp : e.toSpacetime (t, x) ∈ O) :
    (G.spatialTangentEquiv t x).symm
      (F.horizontalProjection (e.toSpacetime (t, x))
        (VectorField.mlieBracket (spacetimeModel n)
          (horizontalSectionVectorField F V) (horizontalSectionVectorField F W)
          (e.toSpacetime (t, x)))) =
      VectorField.mlieBracket (𝓡 n)
        (pullbackHorizontalSection G V t) (pullbackHorizontalSection G W t) x := by
  let : ChartedSpace (EuclideanHalfSpace 1) T.Point := T.chartedSpace
  let : IsManifold (𝓡∂ 1) ∞ T.Point := T.isManifold
  let : IsManifold (spacetimeModel n) (minSmoothness ℝ 2) (T.Point × C) := by
    simp only [minSmoothness_of_isRCLikeNormedField, spacetimeModel]
    infer_instance
  let : IsManifold (spacetimeModel n) (minSmoothness ℝ 2) F.Point := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hb := VectorField.mpullback_mlieBracket
    ((hV.contMDiffOn_vectorField.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp))
    ((hW.contMDiffOn_vectorField.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp))
    (e.smooth (t, x))
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  rw [movingGauge_mpullback_horizontalSection e G V,
    movingGauge_mpullback_horizontalSection e G W, VectorField.mpullback_apply] at hb
  let B := F.horizontalProjection (e.toSpacetime (t, x))
    (VectorField.mlieBracket (spacetimeModel n)
      (horizontalSectionVectorField F V) (horizontalSectionVectorField F W)
      (e.toSpacetime (t, x)))
  have hB : B.val = VectorField.mlieBracket (spacetimeModel n)
      (horizontalSectionVectorField F V) (horizontalSectionVectorField F W)
      (e.toSpacetime (t, x)) := by
    exact congrArg Subtype.val (F.horizontalProjection_identity _
      ⟨_, horizontalSectionBracket_is_horizontal hO hV hW hp⟩)
  have hs := movingGauge_mfderiv_spatial e G t x ((G.spatialTangentEquiv t x).symm B)
  rw [ContinuousLinearEquiv.apply_symm_apply, hB] at hs
  rw [← hs, (movingGauge_mfderiv_isInvertible e (t, x)).inverse_apply_self] at hb
  have hprod := Poincare.Manifold.VectorField.mlieBracket_prod_snd
    (fun _ : T.Point => 0) (pullbackHorizontalSection G V) (pullbackHorizontalSection G W)
    (t, x) (movingGauge_liftedSection_smoothAt e G V O hO hV (t, x) hp)
    (movingGauge_liftedSection_smoothAt e G W O hO hW (t, x) hp)
  exact (congrArg Prod.snd hb).trans (by simpa only [map_zero, zero_add] using hprod)

private theorem rawLeafwiseCovariantDerivative_torsion_on_gauge
    (D : LeafwiseLeviCivitaFamily F S) (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric)
    {V W : HorizontalSection F} {O : Set F.Point} (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O)
    (hW : IsSmoothHorizontalSectionOn F W O)
    (t : T.Point) (x : C) (hp : e.toSpacetime (t, x) ∈ O) :
    rawLeafwiseCovariantDerivative D W (e.toSpacetime (t, x)) (V (e.toSpacetime (t, x))) -
        rawLeafwiseCovariantDerivative D V (e.toSpacetime (t, x)) (W (e.toSpacetime (t, x))) =
      F.horizontalProjection (e.toSpacetime (t, x))
        (VectorField.mlieBracket (spacetimeModel n)
          (horizontalSectionVectorField F V) (horizontalSectionVectorField F W)
          (e.toSpacetime (t, x))) := by
  have hs := movingGaugeSectionTransportFields D e G c
  have hVW := hs.leafwise_derivative_eq W O hO hW t x hp
    (pullbackHorizontalSection G V t x)
  have hWV := hs.leafwise_derivative_eq V O hO hV t x hp
    (pullbackHorizontalSection G W t x)
  simp only [pullbackHorizontalSection, ContinuousLinearEquiv.apply_symm_apply] at hVW hWV
  have hVt := (movingGauge_pullbackHorizontalSection_smoothAt e G V O hO hV (t, x) hp).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)
  have hWt := (movingGauge_pullbackHorizontalSection_smoothAt e G W O hO hW (t, x) hp).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)
  have htors := (c t.val).covariantDerivativeOnFields_sub_swap
    (hVt.mdifferentiableAt (by simp)) (hWt.mdifferentiableAt (by simp))
  rw [hVW, hWV, ← map_sub]
  apply (G.spatialTangentEquiv t x).symm.injective
  rw [ContinuousLinearEquiv.symm_apply_apply, horizontalBracket_pullback G hO hV hW t x hp]
  exact htors

end Gauge

theorem rawLeafwiseCovariantDerivative_torsion
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S) {T : SpacetimeIntervalSystem}
    (cover : SpacetimeGaugeCover F T)
    {V W : HorizontalSection F} {O : Set F.Point} (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O)
    (hW : IsSmoothHorizontalSectionOn F W O) {p : F.Point} (hp : p ∈ O) :
    rawLeafwiseCovariantDerivative D W p (V p) - rawLeafwiseCovariantDerivative D V p (W p) =
      F.horizontalProjection p (VectorField.mlieBracket (spacetimeModel n)
        (horizontalSectionVectorField F V) (horizontalSectionVectorField F W) p) := by
  obtain ⟨b, q, rfl⟩ := cover.covers p
  obtain ⟨c⟩ := hCoordinates.exists_gaugeMetricLeviCivitaFamily
    (cover.metric b).toMovingSpacetimeGaugeGeometry
  exact rawLeafwiseCovariantDerivative_torsion_on_gauge D
    (cover.metric b).toMovingSpacetimeGaugeGeometry c hO hV hW q.1 q.2 hp

theorem rawLeafwiseCovariantDerivative_koszul
    (hCoordinates : M12MetricPredecessors.{0} n)
    (D : LeafwiseLeviCivitaFamily F S) {T : SpacetimeIntervalSystem}
    (cover : SpacetimeGaugeCover F T)
    {V W Z : HorizontalSection F} {O : Set F.Point} (hO : IsOpen O)
    (hV : IsSmoothHorizontalSectionOn F V O)
    (hW : IsSmoothHorizontalSectionOn F W O)
    (hZ : IsSmoothHorizontalSectionOn F Z O) {p : F.Point} (hp : p ∈ O) :
    2 * F.horizontalMetric.inner p (rawLeafwiseCovariantDerivative D W p (V p)) (Z p) =
      mvfderiv (spacetimeModel n) (fun q => F.horizontalMetric.inner q (W q) (Z q)) p (V p).val +
      mvfderiv (spacetimeModel n) (fun q => F.horizontalMetric.inner q (Z q) (V q)) p (W p).val -
      mvfderiv (spacetimeModel n) (fun q => F.horizontalMetric.inner q (V q) (W q)) p (Z p).val +
      F.horizontalMetric.inner p (F.horizontalProjection p
        (VectorField.mlieBracket (spacetimeModel n)
          (horizontalSectionVectorField F V) (horizontalSectionVectorField F W) p)) (Z p) -
      F.horizontalMetric.inner p (F.horizontalProjection p
        (VectorField.mlieBracket (spacetimeModel n)
          (horizontalSectionVectorField F W) (horizontalSectionVectorField F Z) p)) (V p) +
      F.horizontalMetric.inner p (F.horizontalProjection p
        (VectorField.mlieBracket (spacetimeModel n)
          (horizontalSectionVectorField F Z) (horizontalSectionVectorField F V) p)) (W p) := by
  have hv := (hV.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp)
  have hw := (hW.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp)
  have hz := (hZ.contMDiffAt (hO.mem_nhds hp)).mdifferentiableAt (by simp)
  rw [rawLeafwiseCovariantDerivative_metric D hw hz,
    rawLeafwiseCovariantDerivative_metric D hz hv,
    rawLeafwiseCovariantDerivative_metric D hv hw,
    ← rawLeafwiseCovariantDerivative_torsion hCoordinates D cover hO hV hW hp,
    ← rawLeafwiseCovariantDerivative_torsion hCoordinates D cover hO hW hZ hp,
    ← rawLeafwiseCovariantDerivative_torsion hCoordinates D cover hO hZ hV hp]
  simp only [map_sub, sub_apply]
  rw [F.horizontalMetric.symm p (W p), F.horizontalMetric.symm p (Z p),
    F.horizontalMetric.symm p (V p)]
  ring

end PoincareConjecture
