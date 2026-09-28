import PoincareConjecture.Proofs.M14.Sec6_6_RescalingCurvature
import PoincareConjecture.Statements.M12GeneralizedEquation









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (S : GeneralizedFlowSpacetime n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)



noncomputable def rescalingHorizontalSection (V : HorizontalSection S) :
    HorizontalSection (M13.parabolicSpacetime S Q hQ a) :=
  fun p => M13.parabolicSpacetimeHorizontal S Q hQ a p (V p)



theorem rescalingHorizontalSection_smooth (V : HorizontalSection S) (U : Set S.Point)
    (hV : IsSmoothHorizontalSectionOn S V U) :
    IsSmoothHorizontalSectionOn (M13.parabolicSpacetime S Q hQ a)
      (rescalingHorizontalSection S Q hQ a V) U :=
  (M13.parabolicSpacetimeHorizontal_smooth S Q hQ a).comp_contMDiffOn hV



theorem rescalingTimeBracket (V : HorizontalSection S) (p : S.Point) :
    horizontalTimeBracket (M13.parabolicSpacetime S Q hQ a)
      (rescalingHorizontalSection S Q hQ a V) p =
        (1 / Q : ℝ) • M13.parabolicSpacetimeHorizontal S Q hQ a p
          (horizontalTimeBracket S V p) := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n)))
      S.Point := S.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ S.Point := S.isManifold
  change (M13.parabolicSpacetime S Q hQ a).horizontalProjection p
    (VectorField.mlieBracket (spacetimeModel n)
      ((1 / Q : ℝ) • S.timeVector) (horizontalSectionVectorField S V) p) = _
  rw [VectorField.mlieBracket_const_smul_left
    (S.timeVector_smooth.mdifferentiable (by simp) p), map_smul,
    M13.parabolicSpacetime_projection]
  rfl

private theorem metricPair_mdifferentiableAt
    (V W : HorizontalSection S) (U : Set S.Point) (hU : IsOpen U)
    (hV : IsSmoothHorizontalSectionOn S V U)
    (hW : IsSmoothHorizontalSectionOn S W U) (p : S.Point) (hp : p ∈ U) :
    MDifferentiableAt (spacetimeModel n) 𝓘(ℝ)
      (fun q => S.horizontalMetric.inner q (V q) (W q)) p := by
  have ht : MDifferentiableAt (spacetimeModel n) ((spacetimeModel n).prod 𝓘(ℝ))
      (fun q : S.Point => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial S.Point ℝ) q
        (S.horizontalMetric.inner q (V q) (W q))) p := by
    apply MDifferentiableAt.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
    · exact S.horizontalMetric.contMDiff.mdifferentiableAt (by simp)
    · exact (hV.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)
    · exact (hW.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)
  simp only [mdifferentiableAt_totalSpace] at ht
  exact ht.2



theorem rescalingLieOnFields (U : Set S.Point) (hU : IsOpen U)
    (V W : HorizontalSection S) (hV : IsSmoothHorizontalSectionOn S V U)
    (hW : IsSmoothHorizontalSectionOn S W U) (p : S.Point) (hp : p ∈ U) :
    horizontalMetricLieDerivativeOnFields (M13.parabolicSpacetime S Q hQ a)
      (rescalingHorizontalSection S Q hQ a V)
      (rescalingHorizontalSection S Q hQ a W) p =
        horizontalMetricLieDerivativeOnFields S V W p := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin n)))
      S.Point := S.chartedSpace
  let : IsManifold (spacetimeModel n) ∞ S.Point := S.isManifold
  have hpair := metricPair_mdifferentiableAt S V W U hU hV hW p hp
  have hg : (fun q : S.Point => (M13.parabolicSpacetime S Q hQ a).horizontalMetric.inner q
      (rescalingHorizontalSection S Q hQ a V q)
      (rescalingHorizontalSection S Q hQ a W q)) =
      (fun q => Q * S.horizontalMetric.inner q (V q) (W q)) := by
    funext q
    exact M13.parabolicSpacetime_metric S Q hQ a q (V q) (W q)
  unfold horizontalMetricLieDerivativeOnFields
  rw [hg, rescalingTimeBracket, rescalingTimeBracket]
  change mvfderiv (spacetimeModel n)
      (fun q : S.Point => Q * S.horizontalMetric.inner q (V q) (W q)) p
      ((1 / Q : ℝ) • S.timeVector p) -
    (M13.parabolicSpacetime S Q hQ a).horizontalMetric.inner p
      ((1 / Q : ℝ) • M13.parabolicSpacetimeHorizontal S Q hQ a p
        (horizontalTimeBracket S V p))
      (M13.parabolicSpacetimeHorizontal S Q hQ a p (W p)) -
    (M13.parabolicSpacetime S Q hQ a).horizontalMetric.inner p
      (M13.parabolicSpacetimeHorizontal S Q hQ a p (V p))
      ((1 / Q : ℝ) • M13.parabolicSpacetimeHorizontal S Q hQ a p
        (horizontalTimeBracket S W p)) = _
  rw [mvfderiv_fun_mul mdifferentiableAt_const hpair]
  simp only [mvfderiv_const, smul_zero, add_zero, map_smul, smul_apply, smul_eq_mul,
    M13.parabolicSpacetime_metric]
  field_simp [hQ.ne']



theorem rescalingHorizontalLie
    (D : ∀ t, SpacetimeSliceGeometry S t)
    (L : LeafwiseLeviCivitaFamily S D)
    (L' : LeafwiseLeviCivitaFamily (M13.parabolicSpacetime S Q hQ a)
      (M13.parabolicSpacetimeSlice S D Q hQ a))
    (hL : HorizontalRicciCalculus L) (hL' : HorizontalRicciCalculus L')
    (p : S.Point) (v w : S.Horizontal p) :
    horizontalMetricLieDerivative (M13.parabolicSpacetime S Q hQ a) p
      (M13.parabolicSpacetimeHorizontal S Q hQ a p v)
      (M13.parabolicSpacetimeHorizontal S Q hQ a p w) =
        horizontalMetricLieDerivative S p v w := by
  let V : HorizontalSection S := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  let W : HorizontalSection S := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w
  obtain ⟨U, hUp, hV⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞)
    (spacetimeModel n) (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨U', hU'p, hW⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞)
    (spacetimeModel n) (EuclideanSpace ℝ (Fin n)) w
  obtain ⟨O, hOU, hO, hp⟩ := mem_nhds_iff.mp (Filter.inter_mem hUp hU'p)
  have hVO : IsSmoothHorizontalSectionOn S V O := hV.mono (fun _ hx => (hOU hx).1)
  have hWO : IsSmoothHorizontalSectionOn S W O := hW.mono (fun _ hx => (hOU hx).2)
  calc
    _ = horizontalMetricLieDerivative (M13.parabolicSpacetime S Q hQ a) p
        (M13.parabolicSpacetimeHorizontal S Q hQ a p (V p))
        (M13.parabolicSpacetimeHorizontal S Q hQ a p (W p)) := by
      simp only [V, W, FiberBundle.extend_apply_self]
    _ = horizontalMetricLieDerivativeOnFields (M13.parabolicSpacetime S Q hQ a)
        (rescalingHorizontalSection S Q hQ a V)
        (rescalingHorizontalSection S Q hQ a W) p :=
      hL'.lie_on_fields O hO _ _
        (rescalingHorizontalSection_smooth S Q hQ a V O hVO)
        (rescalingHorizontalSection_smooth S Q hQ a W O hWO) p hp
    _ = horizontalMetricLieDerivativeOnFields S V W p :=
      rescalingLieOnFields S Q hQ a O hO V W hVO hWO p hp
    _ = horizontalMetricLieDerivative S p (V p) (W p) :=
      (hL.lie_on_fields O hO V W hVO hWO p hp).symm
    _ = _ := by simp only [V, W, FiberBundle.extend_apply_self]

end PoincareConjecture.M14
