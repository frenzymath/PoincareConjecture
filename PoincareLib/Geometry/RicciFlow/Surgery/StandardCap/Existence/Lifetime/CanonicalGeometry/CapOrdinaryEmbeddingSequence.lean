import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.CapOrdinaryEmbeddingMetric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Curvature.OrdinaryCompactScalarLimits

/-!
# The actual zero-slice ordinary embedding of a blow-up sequence

All maps and normalizations refer to the literal selected subsequence.
The included zero time and M30 base equality are retained exactly.
Source: Theorem 12.28, pp. 323-324; cap-ordinary-embedding.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M34

private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

variable (p : ℕ → (ordinaryChapter11Flow (I := I) (F := F) R).point)
  (hp : ∀ k, 0 < (ordinaryChapter11Flow (I := I) (F := F) R).scalar (p k))
  (hd : Tendsto (fun k => (ordinaryChapter11Flow (I := I) (F := F) R).scalar (p k)) atTop atTop)
  {J : Set ℝ} (C : GeneralizedBlowupConvergence
    (fixedFlowBlowupSequence (ordinaryChapter11Flow (I := I) (F := F) R) p hp hd) J)

private theorem embedding_zero_mem (k : ℕ) :
    (0 : ℝ) ∈ Icc (-C.exhaustion.time k) 0 := by
  constructor
  · exact neg_nonpos.mpr (C.exhaustion.time_pos k).le
  · exact le_rfl

local notation "hz" => embedding_zero_mem R p hp hd C

/-- The genuine ordinary partial embedding at included normalized time
zero, on the whole actual exhaustion source. -/
noncomputable def capOrdinaryEmbedding (k : ℕ) :
    OpenPartialHomeomorph C.limit.sliceCarrier.carrier M :=
  ordinaryChapter11CylinderOpenPartialHomeomorph R (C.embedding k)
    (C.exhaustion.space_open k) 0 (hz k)
    (ordinaryChapter11Point_time_mem R ((C.embedding k).pointMap 0 (hz k) C.limit.base))

/-- Its total map equals the actual cylinder's ordinary projection. -/
theorem capOrdinaryEmbedding_apply (k : ℕ) (x : C.limit.sliceCarrier.carrier) :
    capOrdinaryEmbedding R p hp hd C k x =
      ordinaryChapter11Projection R ((C.embedding k).pointMap 0 (hz k) x) :=
  ordinaryChapter11CylinderOpenPartialHomeomorph_apply R (C.embedding k)
    (C.exhaustion.space_open k) 0 (hz k) _ x

/-- The domain is exactly the actual M30 exhaustion source. -/
theorem capOrdinaryEmbedding_source (k : ℕ) :
    (capOrdinaryEmbedding R p hp hd C k).source = C.exhaustion.space k := rfl

/-- Both directions are smooth on their recorded actual domains. -/
theorem capOrdinaryEmbedding_smooth (k : ℕ) :
    let e := capOrdinaryEmbedding R p hp hd C k
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target :=
  ordinaryChapter11CylinderOpenPartialHomeomorph_smooth R (C.embedding k)
    (C.exhaustion.space_open k) 0 (hz k) _

/-- The actual limit base maps to the exact selected ordinary point. -/
theorem capOrdinaryEmbedding_base (k : ℕ) :
    capOrdinaryEmbedding R p hp hd C k C.limit.base =
      ordinaryChapter11Projection R (p (C.subsequence k)) := by
  rw [capOrdinaryEmbedding_apply, C.base_preserving k (hz k)]
  rfl

/-- Its pullback is the literal positively normalized physical metric
at the selected source time, including time zero. -/
theorem capOrdinaryEmbedding_metric (k : ℕ) {x : C.limit.sliceCarrier.carrier}
    (hx : x ∈ C.exhaustion.space k) (v w : TangentSpace (𝓡 3) x) :
    let e := capOrdinaryEmbedding R p hp hd C k
    (C.embedding k).pullbackInner 0 (hz k) x v w =
      (M13.scaleSmoothMetric (F.metric (p (C.subsequence k)).1)
        ((G).scalar (p (C.subsequence k))) (hp (C.subsequence k))).inner
          (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) := by
  have h := ordinaryChapter11CylinderOpenPartialHomeomorph_metric R (C.embedding k)
    (C.exhaustion.space_open k) 0 (hz k)
    (ordinaryChapter11Point_time_mem R ((C.embedding k).pointMap 0 (hz k) C.limit.base)) hx v w
  simpa only [capOrdinaryEmbedding, GeneralizedBlowupSequence.scale,
    fixedFlowBlowupSequence, zero_div, add_zero] using h

end PoincareMT.M34
