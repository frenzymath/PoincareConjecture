import PoincareConjecture.Proofs.M11.OrdinarySlices
import PoincareConjecture.Proofs.M11.CompatibleTheory
import PoincareConjecture.Statements.M11GeneralizedFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M11

noncomputable def ordinaryProductConclusion {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (g : ℝ → RiemannianMetric n M) (I : SpacetimeInterval)
    (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain) :
    OrdinaryProductSpacetimeConclusion g I where
  timeIntervals := intervalSystem
  spacetime := adaptedSpacetime (ordinaryAtlas g I hg)
  slices := adaptedSliceGeometry (ordinaryAtlas g I hg)
  productIdentification := ordinaryProductIdentification g I hg
  productIdentification_eq := fun _ ↦ rfl
  product_timeVector := ordinaryProduct_timeVector g I hg
  productCylinder := ordinaryProductCylinder g I hg
  productCylinder_eq := fun _ ↦ rfl
  productMetric := ordinaryProductMetric g I hg
  productMetric_eq := rfl
  sliceIdentification := ordinarySliceIdentification g I hg
  sliceIdentification_eq := fun _ _ ↦ rfl
  sliceMetric_eq := ordinarySlice_metric_eq g I hg
  compatible := adaptedCompatibleTheory.{u, u} (ordinaryAtlas g I hg)
  coordinate_compatible := adaptedCompatibleTheory.{u, 0} (ordinaryAtlas g I hg)

end PoincareConjecture.Proofs.M11
