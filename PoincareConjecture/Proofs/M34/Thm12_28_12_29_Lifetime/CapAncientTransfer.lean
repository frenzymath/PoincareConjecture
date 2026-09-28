import PoincareConjecture.Proofs.M34.Standard.CapIsometry
import PoincareConjecture.Proofs.M34.Standard.CapMetricScaling
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryGeometry
import PoincareConjecture.Definitions.Ch11.SingularLimits










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R




theorem ordinaryChapter11_canonicalControl_of_normalized_cap
    (p : (G).point) {Q epsilon C : ℝ} (hQ : 0 < Q)
    (N : CapCertificate (M13.scaleSmoothMetric (F.metric p.1) Q hQ))
    (hepsilon : N.epsilon = epsilon) (hconstant : N.cap_constant ≤ C)
    (hcore : ordinaryChapter11Projection R p ∈ N.core) :
    GeneralizedCanonicalControl (F := G) p.1 p.2 epsilon C := by
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  let t : I.domain := ⟨p.1, ordinaryChapter11Point_time_mem R p⟩
  let N' := N.scaleMetric Q⁻¹ (inv_pos.mpr hQ)
  have hisometry : MetricHomothety
      (M13.scaleSmoothMetric (M13.scaleSmoothMetric (F.metric p.1) Q hQ)
        Q⁻¹ (inv_pos.mpr hQ)) ((G).metric p.1) (R.product.sliceIdentification t) 1 := by
    intro x v w
    have hm := ordinarySlice_metricHomothety R.product t x v w
    simp only [M13.scaleSmoothMetric_inner, ← mul_assoc, inv_mul_cancel₀ hQ.ne', one_mul]
    convert! hm using 1
    simp only [t, one_mul]
  obtain ⟨H, he, hC, hD, hHcore, _⟩ :=
    N'.exists_isometric_image_cap (R.product.sliceIdentification t) hisometry ((G).connection p.1)
  apply GeneralizedCanonicalControl.cap H (he.trans hepsilon) (hC.trans_le hconstant) hD
  rw [hHcore]
  refine ⟨ordinaryChapter11Projection R p, hcore, ?_⟩
  exact ordinaryChapter11_identification_projection R t p.2

end PoincareConjecture.M34
