import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_MaximalSamples
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalInterval
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_RemovalRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M44

variable {g0 : StandardInitialMetric} {F : SurgeryFlowData.{u}} {a : ℝ}
  {ha : a ∈ F.surgery_times} [Nonempty (F.slice a).carrier]
  {i : Fin (F.event a ha).cap_count}

namespace CylinderCompactnessSample

noncomputable def restrictLifetime (D : CylinderCompactnessSample g0 F a ha i)
    {b : ℝ} (hb : 0 < b) (hbD : b ≤ D.lifetime) :
    CylinderCompactnessSample g0 F a ha i :=
  { D with
    lifetime := b
    lifetime_pos := hb
    cylinder := restrictCylinderInterval D.cylinder
      (Ico_subset_Ico_right hbD) ordConnected_Ico
    birth_identity := fun _hs x hx => D.birth_identity _ x hx
    ordinary :=
      { flow := Poincare.Geometry.RicciFlow.Harnack.restrictFlow D.ordinary.flow
          (Ico_subset_Ico_right hbD) ordConnected_Ico (Ico_infinite hb).nontrivial
        metric_link := fun s hs y v w => D.ordinary.metric_link s
          (Ico_subset_Ico_right hbD hs) y v w } }

theorem restrictLifetime_coefficients (D : CylinderCompactnessSample g0 F a ha i)
    {b : ℝ} (hb : 0 < b) (hbD : b ≤ D.lifetime) :
    (D.restrictLifetime hb hbD).coefficients = D.coefficients := rfl

end CylinderCompactnessSample

namespace MaximalCapSample

theorem region_subset_of_radius_le {B1 B2 : ℝ}
    (D1 : MaximalCapSample g0 F a ha i B1) (D2 : MaximalCapSample g0 F a ha i B2)
    (hR : D1.radius ≤ D2.radius) : D1.region ⊆ D2.region := by
  rw [D1.region_eq, D2.region_eq]
  have hh := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  exact fun _ hx => hx.trans_le
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hR hh.le))

theorem lifetime_antitone {B : ℝ}
    (D1 D2 : MaximalCapSample g0 F a ha i B) (hR : D1.radius ≤ D2.radius) :
    D2.lifetime ≤ D1.lifetime := by
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  let e := restrictCylinderSource D2.cylinder (D1.region_subset_of_radius_le D2 hR)
  apply D1.maximal D2.lifetime hlt D2.lifetime_le
  exact ⟨e, fun hs x hx => D2.birth_identity hs x
    (D1.region_subset_of_radius_le D2 hR hx)⟩

end MaximalCapSample

end PoincareConjecture.M44
