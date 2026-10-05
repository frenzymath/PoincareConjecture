import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Basic.OrdinaryGeometry

/-!
# Scalar curvature in the retained ordinary flow box

The single Chapter 11 box is the literal ordinary flow. Its forward
map is the actual factor-one slice identification, so its scalar
curvature equals the selected slice scalar at that image.
Source: Morgan-Tian Theorem 12.28, pp. 323-324; bad-point selection
derivation, section 6.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

/-- Exact scalar pullback for every box representation in the actual
ordinary Chapter 11 realization (Theorem 12.28). -/
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

end PoincareMT.M34
