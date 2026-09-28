import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryGeometry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

theorem ordinaryChapter11_box_scalar_eq
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
    (R : OrdinaryProductRicciGeometry F.metric I)
    (C : ∀ t : I.domain,
      MetricHomothetyCalculus (F.metric t.val) (R.product.slices t.val).metricOnPoints
        (R.product.sliceIdentification t) 1)
    (b : (ordinaryChapter11Flow R).box_index) {t : ℝ}
    (ht : t ∈ ((ordinaryChapter11Flow R).box b).interval)
    (x : ((ordinaryChapter11Flow R).box b).carrier.carrier) :
    (ordinaryChapter11Flow R).scalar
        ⟨t, ((ordinaryChapter11Flow R).box b).forward t ht x⟩ =
      (((ordinaryChapter11Flow R).box b).flow.connection t).scalarCurvature x := by
  change (R.leafwiseConnection.sliceConnection t).scalarCurvature
    (R.product.sliceIdentification ⟨t, ht⟩ x) = (F.connection t).scalarCurvature x
  simpa only [div_one] using (C ⟨t, ht⟩).scalar_eq (F.connection t)
    (R.leafwiseConnection.sliceConnection t) x

end PoincareConjecture.M34
