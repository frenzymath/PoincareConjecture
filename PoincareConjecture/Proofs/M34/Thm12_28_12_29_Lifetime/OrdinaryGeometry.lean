import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryProjection
import PoincareConjecture.Proofs.M34.Standard.OrdinarySliceMetric











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)



theorem ordinaryChapter11Point_time_mem (p : (ordinaryChapter11Flow R).point) :
    p.1 ∈ I.domain := p.2.property ▸ p.2.val.1.property



theorem ordinaryChapter11_identification_projection (t : I.domain)
    (x : ((ordinaryChapter11Flow R).slice t.val).carrier) :
    R.product.sliceIdentification t x.val.2 = x := by
  apply Subtype.ext
  rw [R.product.sliceIdentification_eq]
  exact Prod.ext (Subtype.ext x.property.symm) rfl



theorem ordinaryChapter11_inverse_projection (t : I.domain)
    (x : ((ordinaryChapter11Flow R).slice t.val).carrier) :
    (R.product.sliceIdentification t).symm x = x.val.2 := by
  apply (R.product.sliceIdentification t).injective
  exact (R.product.sliceIdentification t).apply_symm_apply x |>.trans
    (ordinaryChapter11_identification_projection R t x).symm



theorem ordinaryChapter11Point_ext {p q : (ordinaryChapter11Flow R).point}
    (ht : p.1 = q.1)
    (hx : ordinaryChapter11Projection R p = ordinaryChapter11Projection R q) : p = q := by
  apply (ordinaryChapter11Flatten R.product).injective
  exact Prod.ext (Subtype.ext (p.2.property.trans (ht.trans q.2.property.symm))) hx

variable (C : ∀ t : I.domain,
  MetricHomothetyCalculus (F.metric t.val) (R.product.slices t.val).metricOnPoints
    (R.product.sliceIdentification t) 1)

include C



theorem ordinaryChapter11_scalar_eq (p : (ordinaryChapter11Flow R).point) :
    (ordinaryChapter11Flow R).scalar p =
      (F.connection p.1).scalarCurvature (ordinaryChapter11Projection R p) := by
  let t : I.domain := ⟨p.1, ordinaryChapter11Point_time_mem R p⟩
  have h := (C t).scalar_eq (F.connection p.1)
    (R.leafwiseConnection.sliceConnection p.1) p.2.val.2
  rw [ordinaryChapter11_identification_projection R t p.2, div_one] at h
  exact h



theorem ordinaryChapter11_curvatureNorm_eq (p : (ordinaryChapter11Flow R).point) :
    (ordinaryChapter11Flow R).curvatureNorm p =
      (F.connection p.1).curvatureTensorNorm (ordinaryChapter11Projection R p) := by
  let t : I.domain := ⟨p.1, ordinaryChapter11Point_time_mem R p⟩
  have h := (C t).curvature_norm_eq (F.connection p.1)
    (R.leafwiseConnection.sliceConnection p.1) p.2.val.2
  rw [ordinaryChapter11_identification_projection R t p.2, div_one] at h
  exact h

end PoincareConjecture.M34
