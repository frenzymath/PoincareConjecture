import PoincareConjecture.Proofs.M11.OrdinaryProductMetric
import PoincareConjecture.Proofs.M11.SliceGeometry
import PoincareConjecture.Proofs.M11.SliceMaps





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] [SecondCountableTopology M] [Nonempty M]

noncomputable def ordinarySliceIdentification (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain)
    (t : I.domain) : Diffeomorph (𝓡 n) (𝓡 n) M
      (adaptedSliceGeometry (ordinaryAtlas g I hg) t.val).Point ∞ where
  toFun x := ⟨(t, x), rfl⟩
  invFun p := p.val.2
  left_inv := fun _ ↦ rfl
  right_inv := by
    intro p
    apply Subtype.ext
    exact Prod.ext (Subtype.ext p.property.symm) rfl
  contMDiff_toFun := by
    apply (contMDiff_slice_iff (J := 𝓡 n) (ordinaryAtlas g I hg) t.val _).mpr
    exact (ordinaryProductIdentification g I hg).contMDiff.comp
      (contMDiff_const.prodMk contMDiff_id)
  contMDiff_invFun := by
    let := adaptedSliceChartedSpace (ordinaryAtlas g I hg) t.val
    exact ((ordinaryProductIdentification g I hg).symm.contMDiff.comp
      (slice_inclusion_smooth (ordinaryAtlas g I hg) t.val)).snd

theorem ordinarySlice_tangent_eq (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain)
    (t : I.domain) (x : M) (v : EuclideanSpace ℝ (Fin n)) :
    sliceHorizontalEquiv (ordinaryAtlas g I hg) t.val (ordinarySliceIdentification g I hg t x)
        (mfderiv (𝓡 n) (𝓡 n) (ordinarySliceIdentification g I hg t) x v) =
      cylinderSpatialEquiv (ordinaryProductCylinder g I hg) t x v := by
  let := adaptedChartedSpace (ordinaryAtlas g I hg)
  let := adaptedSliceChartedSpace (ordinaryAtlas g I hg) t.val
  apply Subtype.ext
  rw [sliceHorizontalEquiv_eq, cylinderSpatialEquiv_eq]
  have h := mfderiv_comp_apply x
    ((slice_inclusion_smooth (ordinaryAtlas g I hg) t.val
      (ordinarySliceIdentification g I hg t x)).mdifferentiableAt (by simp))
    (((ordinarySliceIdentification g I hg t).contMDiff x).mdifferentiableAt (by simp)) v
  exact h.symm

theorem ordinarySlice_metric_eq (g : ℝ → RiemannianMetric n M)
    (I : SpacetimeInterval) (hg : RiemannianMetric.IsSmoothFamilyOn g I.domain)
    (t : I.domain) (x : M) (v w : EuclideanSpace ℝ (Fin n)) :
    (adaptedSliceGeometry (ordinaryAtlas g I hg) t.val).metricOnPoints.inner
        (ordinarySliceIdentification g I hg t x)
        (mfderiv (𝓡 n) (𝓡 n) (ordinarySliceIdentification g I hg t) x v)
        (mfderiv (𝓡 n) (𝓡 n) (ordinarySliceIdentification g I hg t) x w) =
      (g t.val).inner x v w := by
  rw [(adaptedSliceGeometry (ordinaryAtlas g I hg) t.val).metric_eq]
  change (adaptedSpacetime (ordinaryAtlas g I hg)).horizontalMetric.inner _
    (sliceHorizontalEquiv (ordinaryAtlas g I hg) t.val _ _)
    (sliceHorizontalEquiv (ordinaryAtlas g I hg) t.val _ _) = _
  rw [ordinarySlice_tangent_eq, ordinarySlice_tangent_eq]
  exact ordinaryProduct_metric_eq g I hg t x v w

end PoincareConjecture.Proofs.M11
