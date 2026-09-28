import PoincareConjecture.Proofs.M76.Rigidity.PeriodProductCoordinates

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

noncomputable def periodCutMap (P : OriginalDiskProduct e R j)
    (a p : ℝ) (u : E → X) (z : E) : X :=
  if z.2 ≤ a / 2 then P.map (periodLowerCoordinates a z) else
    if p - a / 2 ≤ z.2 then P.map (periodUpperCoordinates a p z) else u z

theorem periodCutMap_lower (P : OriginalDiskProduct e R j)
    (a p : ℝ) (u : E → X) {z : E} (hz : z.2 ≤ a / 2) :
    P.periodCutMap a p u z = P.map (periodLowerCoordinates a z) := by
  simp only [periodCutMap, if_pos hz]

theorem periodCutMap_upper (P : OriginalDiskProduct e R j)
    {a p : ℝ} (hgap : a / 2 < p - a / 2) (u : E → X)
    {z : E} (hz : p - a / 2 ≤ z.2) :
    P.periodCutMap a p u z = P.map (periodUpperCoordinates a p z) := by
  have hn : ¬ z.2 ≤ a / 2 := by linarith
  simp only [periodCutMap, if_neg hn, if_pos hz]

theorem periodCutMap_middle (P : OriginalDiskProduct e R j)
    {a p : ℝ} (ha : 0 < a) (hgap : a / 2 < p - a / 2) (u : E → X)
    (hlower : ∀ z ∈ D, u (z, a / 2) = P.map (z, 1 / 2))
    (hupper : ∀ z ∈ D, u (z, p - a / 2) = P.map (z, -(1 / 2)))
    {z : E} (hz : z ∈ D ×ˢ Icc (a / 2) (p - a / 2)) :
    P.periodCutMap a p u z = u z := by
  have hfrac : (a / 2) / a = (1 / 2 : ℝ) := by
    rw [div_right_comm, div_self ha.ne']
  by_cases hlo : z.2 ≤ a / 2
  · have heq : z = (z.1, a / 2) := Prod.ext rfl (le_antisymm hlo hz.2.1)
    rw [P.periodCutMap_lower a p u hlo, periodLowerCoordinates_apply, heq]
    change P.map (z.1, (a / 2) / a) = u (z.1, a / 2)
    rw [hfrac]
    exact (hlower z.1 hz.1).symm
  · by_cases hup : p - a / 2 ≤ z.2
    · have heq : z = (z.1, p - a / 2) := Prod.ext rfl (le_antisymm hz.2.2 hup)
      rw [P.periodCutMap_upper hgap u hup, periodUpperCoordinates_apply, heq]
      have htime : (p - a / 2 - p) / a = -(1 / 2 : ℝ) := by
        rw [show p - a / 2 - p = -(a / 2) by ring, neg_div, hfrac]
      change P.map (z.1, (p - a / 2 - p) / a) = u (z.1, p - a / 2)
      rw [htime]
      exact (hupper z.1 hz.1).symm
    · simp only [periodCutMap, if_neg hlo, if_neg hup]

theorem periodCutMap_endpoints (P : OriginalDiskProduct e R j)
    {a p : ℝ} (ha : 0 < a) (hgap : a / 2 < p - a / 2)
    (u : E → X) (z : V2) (hz : z ∈ D) :
    P.periodCutMap a p u (z, 0) = j z ∧ P.periodCutMap a p u (z, p) = j z := by
  constructor
  · rw [P.periodCutMap_lower a p u (by dsimp; linarith), periodLowerCoordinates_apply]
    simpa only [zero_div] using P.central z hz
  · rw [P.periodCutMap_upper hgap u (by dsimp; linarith), periodUpperCoordinates_apply]
    simpa only [sub_self, zero_div] using P.central z hz

end PoincareConjecture.M76.OriginalDiskProduct
