import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.ProjectivePlaneExclusion
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CompactLimitExclusion
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.FixedFlowSequence
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryRealization











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M34

variable {I : SpacetimeInterval}
  {F : RicciFlow 3 (EuclideanSpace ℝ (Fin 3)) I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R



theorem ordinaryChapter11_euclidean_slice (t : ℝ) (ht : t ∈ (G).interval) :
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) ((G).slice t).carrier
      (EuclideanSpace ℝ (Fin 3)) ∞) :=
  ⟨(R.product.sliceIdentification ⟨t, ht⟩).symm⟩


theorem ordinaryChapter11_limit_not_compact
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J) :
    ¬ IsCompact (univ : Set C.limit.sliceCarrier.carrier) := by
  apply generalizedBlowupConvergence_not_compact C
  intro k t ht
  exact ordinaryChapter11_euclidean_slice (I := I) (F := F) R t ht



theorem ordinaryChapter11_limit_not_projectivePlaneLine
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop)
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) (blowupBackwardInterval ⊤))
    {kappa : ℝ} (A : BlowupAncientKappaIdentification C.limit kappa) :
    letI := C.limit.carrier.topologicalSpace
    letI := C.limit.carrier.measurableSpace
    letI := C.limit.carrier.borelSpace
    letI := C.limit.carrier.chartedSpace
    letI := C.limit.carrier.isManifold
    letI := C.limit.carrier.t2Space
    letI := C.limit.carrier.t3Space
    letI := C.limit.carrier.secondCountable
    letI := C.limit.connectedSpace
    ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate A.solution) := by
  apply generalizedBlowupConvergence_not_projectivePlaneLine C A
  intro k t ht
  exact ordinaryChapter11_euclidean_slice (I := I) (F := F) R t ht

end PoincareConjecture.M34
