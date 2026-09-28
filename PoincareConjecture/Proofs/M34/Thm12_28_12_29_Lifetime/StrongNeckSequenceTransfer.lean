import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckSourceAssembly
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckFamilyTransfer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

private theorem scalar_neck_scale_inverse_sq {Q : ℝ} (hQ : 0 < Q) :
    (Q ^ (-1 / 2 : ℝ))⁻¹ ^ 2 = Q := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hQ.le,
    inv_inv, ← Real.sqrt_eq_rpow, Real.sq_sqrt hQ.le]

private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {K : Set ℝ} {L : BlowupLimitFlow.{u} K} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

theorem ordinaryChapter11_eventually_centered_strongNeck
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) (hJI : Icc (-1 : ℝ) 0 ⊆ J)
    (N : EpsilonNeck (C.limit.flow.metric 0)) (hcenter : N.center = C.limit.base)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hdelta : N.epsilon ≤ epsilon / 4)
    (hlimit : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s => roundCylinderPullback (C.limit.flow.metric s) N.coordinate_map)) :
    ∀ᶠ k : ℕ in atTop,
      ∃ Ns : GeneralizedStrongNeck (G) (p (C.subsequence k)).1 epsilon,
        Ns.center = (p (C.subsequence k)).2 := by
  have hstrict : N.epsilon < epsilon := by linarith
  let N' := N.restrict hstrict.le hepsilonHalf
  filter_upwards [ordinaryChapter11_eventually_neck_familyClose R p hpositive hdiverges C
    hJ hJI N hepsilon hdelta hlimit,
    C.eventually_captures_restricted_neck (C.limit.flow.metric 0) N hstrict hJI]
    with k hclose hcapture
  have hzero : (0 : ℝ) ∈ Icc (-C.exhaustion.time k) 0 :=
    hcapture.2 ⟨by norm_num, le_rfl⟩
  have hbase : (C.embedding k).pointMap 0 hzero N'.center = p (C.subsequence k) := by
    change (C.embedding k).pointMap 0 hzero N.center = p (C.subsequence k)
    rw [hcenter]
    exact C.base_preserving k hzero
  let Q := (G).scalar (p (C.subsequence k))
  have hQ : 0 < Q := hpositive (C.subsequence k)
  let sigma := Q ^ (-1 / 2 : ℝ)
  have hsigma : 0 < sigma := Real.rpow_pos_of_pos hQ _
  have hscale : Q = sigma⁻¹ ^ 2 := (scalar_neck_scale_inverse_sq hQ).symm
  have hscalar : 0 < (G).scalar ((C.embedding k).pointMap 0 hzero N'.center) := by
    rw [hbase]
    exact hQ
  have hsigmaScalar : sigma =
      ((G).scalar ((C.embedding k).pointMap 0 hzero N'.center)) ^ (-1 / 2 : ℝ) := by
    rw [hbase]
  obtain ⟨Ns, hNs⟩ := ordinaryChapter11_exists_sourceStrongNeck R (C.embedding k)
    (C.exhaustion.space_open k) (convex_Icc _ _).isPreconnected hzero N'
    hcapture.1 (fun s hs => hcapture.2 ⟨hs.1.le, hs.2⟩)
    sigma hsigma hscale hscalar hsigmaScalar hclose
  have hpoint : ∃ Ns : GeneralizedStrongNeck (G)
      ((C.embedding k).pointMap 0 hzero N'.center).1 epsilon,
      Ns.center = ((C.embedding k).pointMap 0 hzero N'.center).2 := ⟨Ns, hNs⟩
  exact hbase ▸ hpoint

end PoincareConjecture.M34
