import PoincareConjecture.Proofs.M47.SeedVolumeTransport
import PoincareConjecture.Proofs.M47.SeedSearchBounds









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47



theorem seed_search_volume_density_transfer
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    (hpinch : SurgeryFlowPinched F) {origin c K : ℝ}
    {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U)
    (hU : IsOpen U) (hK : 0 ≤ K)
    (hbase : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (hRm : ∀ s (hs : s ∈ Icc c 0), ∀ x ∈ U,
      (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x) ≤ K)
    (hshort : 6 * K * (-c) ≤ 1 / 2)
    (q : (F.slice origin).carrier) {r k : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure ((F.metric origin).ball q r)))
    (hsource : closure ((F.metric origin).ball q r) ⊆ U)
    (s : ℝ) (hs : s ∈ Icc c 0)
    (hvolume : ENNReal.ofReal (k * (r / 2) ^ 3) ≤
      calibratedMetricVolume (F.metric (origin + s / 1))
        ((F.metric (origin + s / 1)).ball (e.forward s hs q) (r / 2))) :
    ENNReal.ofReal ((k / 64) * r ^ 3) ≤
      calibratedMetricVolume (F.metric origin) ((F.metric origin).ball q r) := by
  let chart := M44.cylinderSliceChart e hU s hs
  have hcomparison := seed_search_metric_comparison P hpinch e hU hK hbase hRm hshort s hs
  have hnonnegative (x : (F.slice origin).carrier) (v : TangentSpace (𝓡 3) x) :
      0 ≤ (F.metric origin).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((F.metric origin).pos x v hv).le
  apply seed_volume_density_transfer (F.metric origin) (F.metric (origin + s / 1))
    chart ?_ ?_ q hr hcompact hsource hvolume
  · intro x hx v
    change (F.metric origin).inner x v v ≤
      4 * (F.metric (origin + s / 1)).inner (e.forward s hs x)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
    have h := hcomparison x hx v
    nlinarith [hnonnegative x v]
  · intro x hx v
    change (F.metric (origin + s / 1)).inner (e.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) ≤
        4 * (F.metric origin).inner x v v
    have h := hcomparison x hx v
    nlinarith [hnonnegative x v]

end PoincareConjecture.Proofs.M47
