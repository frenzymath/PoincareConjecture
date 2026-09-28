import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodMap
import PoincareConjecture.Proofs.M76.Rigidity.MeridianParameter

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

theorem periodCutMap_lateral {α : Type*}
    {e : α → OpenPartialHomeomorph X V3} {j : V2 → X}
    (P : OriginalDiskProduct e R j) {a : ℝ}
    (ha : 0 < a) (hgap : a / 2 < p - a / 2) (u : E → X)
    (hlower : ∀ z ∈ D, u (z, a / 2) = P.map (z, 1 / 2))
    (hupper : ∀ z ∈ D, u (z, p - a / 2) = P.map (z, -(1 / 2)))
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t))
    (hlateral : ∀ z ∈ Q, ∀ t ∈ Icc (a / 2) (p - a / 2),
      u (z, t) = hamiltonMeridianCutAmbientMap (z, t))
    {z : E} (hz : z ∈ Q ×ˢ Icc 0 p) :
    P.periodCutMap a p u z = hamiltonMeridianCutAmbientMap z := by
  have hzD : z.1 ∈ D := sphere_subset_closedBall hz.1
  by_cases hlo : z.2 ≤ a / 2
  · have hb := @periodLowerCoordinates_mapsTo a ha z ⟨hzD, hz.2.1, hlo⟩
    rw [periodLowerCoordinates_apply] at hb
    have ht : z.2 / a ∈ I := ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩
    rw [P.periodCutMap_lower a p u hlo, periodLowerCoordinates_apply,
      hmark z.1 hz.1 _ ht, mul_div_cancel₀ _ ha.ne']
  · by_cases hup : p - a / 2 ≤ z.2
    · have hb := @periodUpperCoordinates_mapsTo a p ha z ⟨hzD, hup, hz.2.2⟩
      rw [periodUpperCoordinates_apply] at hb
      have ht : (z.2 - p) / a ∈ I :=
        ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩
      rw [P.periodCutMap_upper hgap u hup, periodUpperCoordinates_apply,
        hmark z.1 hz.1 _ ht, mul_div_cancel₀ _ ha.ne']
      have hperiod := congrArg (fun x : R => (x : X))
        (hamiltonMeridianParameter_period z.1 (z.2 - p))
      have hleft := hamiltonMeridianParameter_val
        (z.1, z.2 - p + p) hzD
      have hright := hamiltonMeridianParameter_val
        (z.1, z.2 - p) hzD
      calc
        hamiltonMeridianCutAmbientMap (z.1, z.2 - p) =
            (hamiltonMeridianParameter (z.1, z.2 - p) : X) := hright.symm
        _ = (hamiltonMeridianParameter (z.1, z.2 - p + p) : X) := hperiod.symm
        _ = hamiltonMeridianCutAmbientMap (z.1, z.2 - p + p) := hleft
        _ = hamiltonMeridianCutAmbientMap z := by rw [sub_add_cancel]
    · have hmid : z.2 ∈ Icc (a / 2) (p - a / 2) :=
        ⟨(not_le.mp hlo).le, (not_le.mp hup).le⟩
      rw [P.periodCutMap_middle ha hgap u hlower hupper ⟨hzD, hmid⟩]
      exact hlateral z.1 hz.1 z.2 hmid

end PoincareConjecture.M76.OriginalDiskProduct
