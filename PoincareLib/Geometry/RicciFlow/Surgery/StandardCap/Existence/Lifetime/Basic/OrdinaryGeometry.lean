import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Basic.OrdinaryProjection
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Flow.OrdinarySliceMetric

/-!
# Exact ordinary geometry in the Chapter 11 realization

The actual slice identifications preserve scalar curvature and the full
curvature norm for the selected compatible connections. Projection
therefore reads these quantities in the original ordinary flow.
Source: Morgan-Tian Theorems 12.28-12.29, pp. 323-325; ordinary Chapter 11
derivation, section 6.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

/-- An actual Chapter 11 point has a clock in the original ordinary flow
interval (Theorems 12.28-12.29). -/
theorem ordinaryChapter11Point_time_mem (p : (ordinaryChapter11Flow R).point) :
    p.1 ∈ I.domain := p.2.property ▸ p.2.val.1.property

/-- Projection followed by the retained slice identification is the
identity on that actual slice (Theorems 12.28-12.29). -/
theorem ordinaryChapter11_identification_projection (t : I.domain)
    (x : ((ordinaryChapter11Flow R).slice t.val).carrier) :
    R.product.sliceIdentification t x.val.2 = x := by
  apply Subtype.ext
  rw [R.product.sliceIdentification_eq]
  exact Prod.ext (Subtype.ext x.property.symm) rfl

/-- The inverse retained slice map is literal ordinary spatial projection
(Theorems 12.28-12.29). -/
theorem ordinaryChapter11_inverse_projection (t : I.domain)
    (x : ((ordinaryChapter11Flow R).slice t.val).carrier) :
    (R.product.sliceIdentification t).symm x = x.val.2 := by
  apply (R.product.sliceIdentification t).injective
  exact (R.product.sliceIdentification t).apply_symm_apply x |>.trans
    (ordinaryChapter11_identification_projection R t x).symm

/-- The physical clock and ordinary spatial coordinate determine each
actual point of the Chapter 11 realization (Theorems 12.28-12.29). -/
theorem ordinaryChapter11Point_ext {p q : (ordinaryChapter11Flow R).point}
    (ht : p.1 = q.1)
    (hx : ordinaryChapter11Projection R p = ordinaryChapter11Projection R q) : p = q := by
  apply (ordinaryChapter11Flatten R.product).injective
  exact Prod.ext (Subtype.ext (p.2.property.trans (ht.trans q.2.property.symm))) hx

variable (C : ∀ t : I.domain,
  MetricHomothetyCalculus (F.metric t.val) (R.product.slices t.val).metricOnPoints
    (R.product.sliceIdentification t) 1)

include C

/-- Scalar curvature of the actual Chapter 11 realization is the scalar
curvature of the original ordinary point (Theorems 12.28-12.29). -/
theorem ordinaryChapter11_scalar_eq (p : (ordinaryChapter11Flow R).point) :
    (ordinaryChapter11Flow R).scalar p =
      (F.connection p.1).scalarCurvature (ordinaryChapter11Projection R p) := by
  let t : I.domain := ⟨p.1, ordinaryChapter11Point_time_mem R p⟩
  have h := (C t).scalar_eq (F.connection p.1)
    (R.leafwiseConnection.sliceConnection p.1) p.2.val.2
  rw [ordinaryChapter11_identification_projection R t p.2, div_one] at h
  exact h

/-- The full curvature norm of the actual Chapter 11 realization is the
original ordinary full curvature norm (Theorems 12.28-12.29). -/
theorem ordinaryChapter11_curvatureNorm_eq (p : (ordinaryChapter11Flow R).point) :
    (ordinaryChapter11Flow R).curvatureNorm p =
      (F.connection p.1).curvatureTensorNorm (ordinaryChapter11Projection R p) := by
  let t : I.domain := ⟨p.1, ordinaryChapter11Point_time_mem R p⟩
  have h := (C t).curvature_norm_eq (F.connection p.1)
    (R.leafwiseConnection.sliceConnection p.1) p.2.val.2
  rw [ordinaryChapter11_identification_projection R t p.2, div_one] at h
  exact h

end PoincareMT.M34
