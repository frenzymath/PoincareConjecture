import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapOrdinaryEmbeddingSequence
import PoincareConjecture.Definitions.Ch11.SingularLimits











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



theorem capPersistence_ordinary_cylinder_pullback_eq
    (p : ℕ → (G).point) (hp : ∀ k, 0 < (G).scalar (p k))
    (hd : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence (fixedFlowBlowupSequence (G) p hp hd) J)
    (k : ℕ) {coordinate : RoundCylinderSpace → C.limit.sliceCarrier.carrier}
    {z : RoundCylinderSpace}
    (hcoordinate : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z)
    (hz : coordinate z ∈ C.exhaustion.space k) (v w : RoundCylinderTangent z) :
    let h := M13.scaleSmoothMetric (F.metric (p (C.subsequence k)).1)
      ((G).scalar (p (C.subsequence k))) (hp (C.subsequence k))
    roundCylinderPullback h (capOrdinaryEmbedding R p hp hd C k ∘ coordinate) z v w =
      generalizedCylinderPullback (C.embedding k) coordinate 0 z v w := by
  let e := capOrdinaryEmbedding R p hp hd C k
  have h0 : (0 : ℝ) ∈ Icc (-C.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  have he : MDifferentiableAt (𝓡 3) (𝓡 3) e (coordinate z) :=
    ((capOrdinaryEmbedding_smooth R p hp hd C k).1.contMDiffAt
      ((C.exhaustion.space_open k).mem_nhds hz)).mdifferentiableAt (by simp)
  have hb := capOrdinaryEmbedding_metric R p hp hd C k hz
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w)
  simp only [roundCylinderPullback, generalizedCylinderPullback, dif_pos h0,
    Function.comp_apply]
  rw [mfderiv_comp z he hcoordinate]
  exact hb.symm

end PoincareConjecture.M34
