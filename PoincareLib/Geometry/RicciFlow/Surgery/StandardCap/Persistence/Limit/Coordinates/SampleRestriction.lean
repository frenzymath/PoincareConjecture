import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cutoff.MaximalSamples
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Continuation.RemovalInterval
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Removal.Continuation.RemovalRestriction

/-!
# Restricting actual cylinder samples

Time restriction preserves the literal ordinary flow and its coordinate
field. Source restriction implies antitonicity of the maximal survival
duration with respect to radius. Morgan--Tian, Claim 16.6 and
Proposition 16.5, pp. 371-374; M44 derivation 100.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.M44

variable {g0 : StandardInitialMetric} {F : SurgeryFlowData.{u}} {a : ℝ}
  {ha : a ∈ F.surgery_times} [Nonempty (F.slice a).carrier]
  {i : Fin (F.event a ha).cap_count}

namespace CylinderCompactnessSample

/-- Restrict the lifetime of an actual sample while keeping its
physical maps, total metric and connection representatives unchanged.
Source: Claim 16.6, p. 371; M44 derivation 100. -/
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

/-- Lifetime restriction preserves the actual total coefficient
field. Source: Claim 16.6, p. 371; M44 derivation 100. -/
theorem restrictLifetime_coefficients (D : CylinderCompactnessSample g0 F a ha i)
    {b : ℝ} (hb : 0 < b) (hbD : b ≤ D.lifetime) :
    (D.restrictLifetime hb hbD).coefficients = D.coefficients := rfl

end CylinderCompactnessSample

namespace MaximalCapSample

/-- Nested actual birth balls give nested tracked regions, even
when their chart choices differ. Source: Proposition 16.5, p. 374;
M44 derivation 100. -/
theorem region_subset_of_radius_le {B1 B2 : ℝ}
    (D1 : MaximalCapSample g0 F a ha i B1) (D2 : MaximalCapSample g0 F a ha i B2)
    (hR : D1.radius ≤ D2.radius) : D1.region ⊆ D2.region := by
  rw [D1.region_eq, D2.region_eq]
  have hh := F.parameters.h_pos a (F.time_domain_nonnegative (F.surgery_times_subset ha))
  exact fun _ hx => hx.trans_le
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hR hh.le))

/-- A larger birth ball cannot have a longer maximal lifetime
below the same assigned endpoint. Source: Proposition 16.5,
p. 374; M44 derivation 100. -/
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

end PoincareMT.M44
