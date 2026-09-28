import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodMap









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


theorem lowerPiece_injective (P : OriginalDiskProduct e R j)
    {a : ℝ} (ha : 0 < a) :
    InjOn (P.map ∘ periodLowerCoordinates a) (D ×ˢ Icc 0 (a / 2)) := by
  intro z hz w hw heq
  have hzc := periodLowerCoordinates_mapsTo ha hz
  have hwc := periodLowerCoordinates_mapsTo ha hw
  have hzI : periodLowerCoordinates a z ∈ D ×ˢ I :=
    ⟨hzc.1, by linarith [hzc.2.1], by linarith [hzc.2.2]⟩
  have hwI : periodLowerCoordinates a w ∈ D ×ˢ I :=
    ⟨hwc.1, by linarith [hwc.2.1], by linarith [hwc.2.2]⟩
  have hc := P.injective hzI hwI heq
  rw [periodLowerCoordinates_apply, periodLowerCoordinates_apply] at hc
  have hf := congrArg (fun x : E => x.1) hc
  change z.1 = w.1 at hf
  have ht : z.2 / a = w.2 / a := congrArg (fun x : E => x.2) hc
  exact Prod.ext hf ((div_left_inj' ha.ne').mp ht)


theorem upperPiece_injective (P : OriginalDiskProduct e R j)
    {a p : ℝ} (ha : 0 < a) :
    InjOn (P.map ∘ periodUpperCoordinates a p) (D ×ˢ Icc (p - a / 2) p) := by
  intro z hz w hw heq
  have hzc := periodUpperCoordinates_mapsTo ha hz
  have hwc := periodUpperCoordinates_mapsTo ha hw
  have hzI : periodUpperCoordinates a p z ∈ D ×ˢ I :=
    ⟨hzc.1, by linarith [hzc.2.1], by linarith [hzc.2.2]⟩
  have hwI : periodUpperCoordinates a p w ∈ D ×ˢ I :=
    ⟨hwc.1, by linarith [hwc.2.1], by linarith [hwc.2.2]⟩
  have hc := P.injective hzI hwI heq
  rw [periodUpperCoordinates_apply, periodUpperCoordinates_apply] at hc
  have hf := congrArg (fun x : E => x.1) hc
  change z.1 = w.1 at hf
  have ht : (z.2 - p) / a = (w.2 - p) / a := congrArg (fun x : E => x.2) hc
  have htime := (div_left_inj' ha.ne').mp ht
  exact Prod.ext hf (by linarith)



theorem lowerPiece_eq_upperPiece_iff (P : OriginalDiskProduct e R j)
    {a p : ℝ} (ha : 0 < a) {z w : E}
    (hz : z ∈ D ×ˢ Icc 0 (a / 2)) (hw : w ∈ D ×ˢ Icc (p - a / 2) p) :
    P.map (periodLowerCoordinates a z) = P.map (periodUpperCoordinates a p w) ↔
      z.1 = w.1 ∧ z.2 = 0 ∧ w.2 = p := by
  constructor
  · intro heq
    have hzc := periodLowerCoordinates_mapsTo ha hz
    have hwc := periodUpperCoordinates_mapsTo ha hw
    have hzI : periodLowerCoordinates a z ∈ D ×ˢ I :=
      ⟨hzc.1, by linarith [hzc.2.1], by linarith [hzc.2.2]⟩
    have hwI : periodUpperCoordinates a p w ∈ D ×ˢ I :=
      ⟨hwc.1, by linarith [hwc.2.1], by linarith [hwc.2.2]⟩
    have hc := P.injective hzI hwI heq
    rw [periodLowerCoordinates_apply, periodUpperCoordinates_apply] at hc
    have hf := congrArg (fun x : E => x.1) hc
    change z.1 = w.1 at hf
    have ht : z.2 / a = (w.2 - p) / a := congrArg (fun x : E => x.2) hc
    have htime := (div_left_inj' ha.ne').mp ht
    exact ⟨hf, by linarith [hz.2.1, hw.2.2], by linarith [hz.2.1, hw.2.2]⟩
  · rintro ⟨hf, hz0, hwp⟩
    rw [periodLowerCoordinates_apply, periodUpperCoordinates_apply, hz0, hwp,
      sub_self, zero_div, hf]

end PoincareConjecture.M76.OriginalDiskProduct
