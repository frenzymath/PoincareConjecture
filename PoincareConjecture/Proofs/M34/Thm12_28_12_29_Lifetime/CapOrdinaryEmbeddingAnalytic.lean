import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapOrdinaryEmbeddingSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

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

theorem capOrdinaryEmbedding_scalarAnalytic (k : ℕ)
    (h0 : (0 : ℝ) ∈ Icc (-C.exhaustion.time k) 0) (x : C.limit.sliceCarrier.carrier) :
    let Q := (G).scalar (p (C.subsequence k))
    let g := M13.scaleSmoothMetric (F.metric (p (C.subsequence k)).1) Q (hp (C.subsequence k))
    let D := M13.scaleLeviCivitaData (F.connection (p (C.subsequence k)).1) Q (hp (C.subsequence k))
    let y := capOrdinaryEmbedding R p hp hd C k x
    let z := (C.embedding k).pointMap 0 h0 x
    (D.scalarCurvature y, scalarGradientNorm g D y,
      D.laplacian D.scalarCurvature y + 2 * D.ricciNormSq y) =
      ((G).scalar z / Q,
        scalarGradientNorm ((G).metric z.1) ((G).connection z.1) z.2 / Q ^ (3 / 2 : ℝ),
        (((G).connection z.1).laplacian ((G).connection z.1).scalarCurvature z.2 +
          2 * ((G).connection z.1).ricciNormSq z.2) / Q ^ 2) := by
  let z := (C.embedding k).pointMap 0 h0 x
  let Q := (G).scalar (p (C.subsequence k))
  let V (t : ℝ) : ℝ × ℝ × ℝ :=
    let g := M13.scaleSmoothMetric (F.metric t) Q (hp (C.subsequence k))
    let D := M13.scaleLeviCivitaData (F.connection t) Q (hp (C.subsequence k))
    let y := ordinaryChapter11Projection R z
    (D.scalarCurvature y, scalarGradientNorm g D y,
      D.laplacian D.scalarCurvature y + 2 * D.ricciNormSq y)
  have ht : z.1 = (p (C.subsequence k)).1 := by
    change (p (C.subsequence k)).1 + 0 / _ = _
    rw [zero_div, add_zero]
  have h := ordinaryChapter11_scaled_scalarAnalytic R z (hp (C.subsequence k))
  change V z.1 = _ at h
  have hresult := (congrArg V ht).symm.trans h
  simpa only [V, capOrdinaryEmbedding_apply] using hresult

theorem capOrdinaryEmbedding_eventually_scalarAnalytic_close
    (hJ : UniqueDiffOn ℝ J) {K : Set C.limit.sliceCarrier.carrier}
    (hK : IsCompact K) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ k : ℕ in atTop, K ⊆ C.exhaustion.space k ∧ ∀ x ∈ K,
      let Q := (G).scalar (p (C.subsequence k))
      let g := M13.scaleSmoothMetric (F.metric (p (C.subsequence k)).1) Q (hp (C.subsequence k))
      let D := M13.scaleLeviCivitaData (F.connection (p (C.subsequence k)).1)
        Q (hp (C.subsequence k))
      let y := capOrdinaryEmbedding R p hp hd C k x
      ‖(D.scalarCurvature y, scalarGradientNorm g D y,
          D.laplacian D.scalarCurvature y + 2 * D.ricciNormSq y) -
        ((C.limit.flow.connection 0).scalarCurvature x,
          scalarGradientNorm (C.limit.flow.metric 0) (C.limit.flow.connection 0) x,
          (C.limit.flow.connection 0).laplacian (C.limit.flow.connection 0).scalarCurvature x +
            2 * (C.limit.flow.connection 0).ricciNormSq x)‖ < eta := by
  filter_upwards [ordinaryChapter11_eventually_compact_scalarAnalytic_close
    R p hp hd C hJ hK eta heta] with k hk
  refine ⟨hk.1, ?_⟩
  intro x hx
  let W : ℝ × ℝ × ℝ :=
    ((C.limit.flow.connection 0).scalarCurvature x,
      scalarGradientNorm (C.limit.flow.metric 0) (C.limit.flow.connection 0) x,
      (C.limit.flow.connection 0).laplacian (C.limit.flow.connection 0).scalarCurvature x +
        2 * (C.limit.flow.connection 0).ricciNormSq x)
  have he := capOrdinaryEmbedding_scalarAnalytic R p hp hd C k
    ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩ x
  exact (congrArg (fun v : ℝ × ℝ × ℝ => ‖v - W‖) he).trans_lt (hk.2 x hx)

end PoincareConjecture.M34
