import PoincareConjecture.Proofs.M47.SeedCylinderRecenter
import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalChart
import PoincareConjecture.Definitions.Ch16.NoncollapseInduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {C : GeneralizedSliceCarrier.{u}}
  {origin Q : ℝ} {I : Set ℝ} {U : Set C.carrier}

theorem seedLimit_physical_recentered_test
    (e : GeneralizedFlowCylinder H.generalized C origin Q I U)
    (hI : I.OrdConnected) (hU : IsOpen U) (x : C.carrier)
    (a : ℝ) (ha : a ∈ I) (ht : origin + a / Q ∈ H.generalized.interval)
    {r K : ℝ} (hrange : ∀ s ∈ Icc (-r ^ 2) 0, a + Q * s ∈ I)
    (p : (F.slice (origin + a / Q)).carrier)
    (hball : (F.metric (origin + a / Q)).ball p r ⊆
      limitRP2PhysicalMap e H.history a ha ht '' U)
    (hK : ∀ s (hs : s ∈ I), ∀ y ∈ U,
      (H.generalized.connection (origin + s / Q)).curvatureTensorNorm
        (e.forward s hs y) ≤ K) :
    ∃ d : SurgeryFlowCylinder F (F.slice (origin + a / Q))
        (origin + a / Q) 1 (Icc (-r ^ 2) 0)
        ((F.metric (origin + a / Q)).ball p r),
      (∀ h y, y ∈ (F.metric (origin + a / Q)).ball p r →
        HEq (d.forward 0 h y) y) ∧
      (∀ s hs y, y ∈ (F.metric (origin + a / Q)).ball p r →
        (F.connection ((origin + a / Q) + s / 1)).curvatureTensorNorm
          (d.forward s hs y) ≤ K) := by
  have htime (s : ℝ) (hs : s ∈ I) : origin + s / Q ∈ H.generalized.interval :=
    (H.generalized.slice_nonempty_iff _).mp ⟨e.forward s hs x⟩
  obtain ⟨raw, hmap, _hmetric⟩ :=
    H.cylinders_to_surgery C origin Q I U hI hU htime e
  apply exists_seedCylinder_recenter raw hU a ha hrange
    ((F.metric (origin + a / Q)).ball p r)
  · intro y hy
    obtain ⟨z, hz, heq⟩ := hball hy
    exact ⟨z, hz, (hmap a ha z hz).trans heq⟩
  · intro s hs y hy
    rw [hmap s hs y hy, H.curvature_norm_pullback]
    exact hK s hs y hy

theorem seedLimit_volume_of_physical_test
    (e : GeneralizedFlowCylinder H.generalized C origin Q I U)
    (hI : I.OrdConnected) (hU : IsOpen U) (x : C.carrier)
    (a : ℝ) (ha : a ∈ I) (ht : origin + a / Q ∈ H.generalized.interval)
    {r kappa : ℝ} (hr : 0 < r) (hcut : r ≤ F.parameters.epsilon)
    {J : Set ℝ} (hvolume : SurgeryVolumeControlOn F J kappa (fun _ _ => True))
    (hJ : origin + a / Q ∈ J)
    (hrange : ∀ s ∈ Icc (-r ^ 2) 0, a + Q * s ∈ I)
    (p : (F.slice (origin + a / Q)).carrier)
    (hball : (F.metric (origin + a / Q)).ball p r ⊆
      limitRP2PhysicalMap e H.history a ha ht '' U)
    (hK : ∀ s (hs : s ∈ I), ∀ y ∈ U,
      (H.generalized.connection (origin + s / Q)).curvatureTensorNorm
        (e.forward s hs y) ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (kappa * r ^ 3) ≤
      calibratedMetricVolume (F.metric (origin + a / Q))
        ((F.metric (origin + a / Q)).ball p r) := by
  obtain ⟨d, hbased, hcurvature⟩ :=
    seedLimit_physical_recentered_test H e hI hU x a ha ht hrange p hball hK
  have htime : origin + a / Q ∈ F.time_domain :=
    W.time_subset (H.interval_eq ▸ ht)
  exact hvolume _ hJ htime p trivial r hr hcut d hbased hcurvature

end PoincareConjecture.Proofs.M47
