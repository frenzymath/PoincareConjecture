import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut
import PoincareConjecture.Proofs.M76.Rigidity.PeriodProductCoordinates

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem map_mem_cutCarrier_iff_ends (P : OriginalDiskProduct e R j)
    {z : E} (hz : z ∈ D ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    P.map z ∈ P.cutCarrier ↔ z.2 = -(1 / 2 : ℝ) ∨ z.2 = 1 / 2 := by
  have hzI : z ∈ D ×ˢ I :=
    ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  constructor
  · intro hx
    by_contra hn
    push Not at hn
    apply hx.2
    exact ⟨z, ⟨hz.1, lt_of_le_of_ne hz.2.1 (Ne.symm hn.1),
      lt_of_le_of_ne hz.2.2 hn.2⟩, rfl⟩
  · intro ht
    refine ⟨P.inside hzI, ?_⟩
    rintro ⟨w, hw, heq⟩
    have hwI : w ∈ D ×ˢ I :=
      ⟨hw.1, by linarith [hw.2.1], by linarith [hw.2.2]⟩
    have htime : w.2 = z.2 := congrArg Prod.snd (P.injective hwI hzI heq)
    rcases ht with ht | ht <;> linarith [hw.2.1, hw.2.2]

theorem lowerCoordinates_mem_cut_iff (P : OriginalDiskProduct e R j)
    {a : ℝ} (ha : 0 < a) {z : E} (hz : z ∈ D ×ˢ Icc 0 (a / 2)) :
    P.map (periodLowerCoordinates a z) ∈ P.cutCarrier ↔ z.2 = a / 2 := by
  have hc := periodLowerCoordinates_mapsTo ha hz
  have hsmall : periodLowerCoordinates a z ∈ D ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨hc.1, by linarith [hc.2.1], hc.2.2⟩
  rw [P.map_mem_cutCarrier_iff_ends hsmall, periodLowerCoordinates_apply]
  change z.2 / a = -(1 / 2 : ℝ) ∨ z.2 / a = 1 / 2 ↔ z.2 = a / 2
  have hnonneg : 0 ≤ z.2 / a := div_nonneg hz.2.1 ha.le
  constructor
  · rintro (ht | ht)
    · linarith
    · have h := (div_eq_iff ha.ne').mp ht
      linarith
  · intro ht
    right
    rw [ht, div_right_comm, div_self ha.ne']

theorem upperCoordinates_mem_cut_iff (P : OriginalDiskProduct e R j)
    {a p : ℝ} (ha : 0 < a) {z : E} (hz : z ∈ D ×ˢ Icc (p - a / 2) p) :
    P.map (periodUpperCoordinates a p z) ∈ P.cutCarrier ↔ z.2 = p - a / 2 := by
  have hc := periodUpperCoordinates_mapsTo ha hz
  have hsmall : periodUpperCoordinates a p z ∈ D ×ˢ Icc (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨hc.1, hc.2.1, by linarith [hc.2.2]⟩
  rw [P.map_mem_cutCarrier_iff_ends hsmall, periodUpperCoordinates_apply]
  change (z.2 - p) / a = -(1 / 2 : ℝ) ∨ (z.2 - p) / a = 1 / 2 ↔
    z.2 = p - a / 2
  have hnonpos : (z.2 - p) / a ≤ 0 :=
    (div_le_iff₀ ha).mpr (by linarith [hz.2.2])
  constructor
  · rintro (ht | ht)
    · have h := (div_eq_iff ha.ne').mp ht
      linarith
    · linarith
  · intro ht
    left
    apply (div_eq_iff ha.ne').mpr
    rw [ht]
    ring

end PoincareConjecture.M76.OriginalDiskProduct
