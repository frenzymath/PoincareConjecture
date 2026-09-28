import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodMap
import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodCutContact









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}



theorem middlePiece_injective (P : OriginalDiskProduct e R j)
    {a p : ℝ} (H : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E) ≃ₜ P.cutCarrier)
    (u : E → X)
    (hvalue : ∀ z : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E), u z = (H z : X)) :
    InjOn u (D ×ˢ Icc (a / 2) (p - a / 2)) := by
  intro z hz w hw heq
  rw [hvalue ⟨z, hz⟩, hvalue ⟨w, hw⟩] at heq
  exact congrArg Subtype.val (H.injective (Subtype.ext heq))



theorem eq_of_lowerPiece_eq_middle (P : OriginalDiskProduct e R j)
    {a p : ℝ} (ha : 0 < a) (hgap : a / 2 < p - a / 2)
    (H : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E) ≃ₜ P.cutCarrier)
    (u : E → X)
    (hvalue : ∀ z : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E), u z = (H z : X))
    (hlower : ∀ z ∈ D, u (z, a / 2) = P.map (z, 1 / 2))
    (hupper : ∀ z ∈ D, u (z, p - a / 2) = P.map (z, -(1 / 2)))
    {z w : E} (hz : z ∈ D ×ˢ Icc 0 (a / 2))
    (hw : w ∈ D ×ˢ Icc (a / 2) (p - a / 2))
    (heq : P.map (periodLowerCoordinates a z) = u w) : z = w := by
  have hcut : P.map (periodLowerCoordinates a z) ∈ P.cutCarrier := by
    rw [heq, hvalue ⟨w, hw⟩]
    exact (H ⟨w, hw⟩).property
  have ht := (P.lowerCoordinates_mem_cut_iff ha hz).mp hcut
  have hzM : z ∈ D ×ˢ Icc (a / 2) (p - a / 2) :=
    ⟨hz.1, by rw [ht], by rw [ht]; exact hgap.le⟩
  have hsame : P.map (periodLowerCoordinates a z) = u z :=
    (P.periodCutMap_lower a p u hz.2.2).symm.trans
      (P.periodCutMap_middle ha hgap u hlower hupper hzM)
  exact P.middlePiece_injective H u hvalue hzM hw (hsame.symm.trans heq)



theorem eq_of_upperPiece_eq_middle (P : OriginalDiskProduct e R j)
    {a p : ℝ} (ha : 0 < a) (hgap : a / 2 < p - a / 2)
    (H : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E) ≃ₜ P.cutCarrier)
    (u : E → X)
    (hvalue : ∀ z : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E), u z = (H z : X))
    (hlower : ∀ z ∈ D, u (z, a / 2) = P.map (z, 1 / 2))
    (hupper : ∀ z ∈ D, u (z, p - a / 2) = P.map (z, -(1 / 2)))
    {z w : E} (hz : z ∈ D ×ˢ Icc (p - a / 2) p)
    (hw : w ∈ D ×ˢ Icc (a / 2) (p - a / 2))
    (heq : P.map (periodUpperCoordinates a p z) = u w) : z = w := by
  have hcut : P.map (periodUpperCoordinates a p z) ∈ P.cutCarrier := by
    rw [heq, hvalue ⟨w, hw⟩]
    exact (H ⟨w, hw⟩).property
  have ht := (P.upperCoordinates_mem_cut_iff ha hz).mp hcut
  have hzM : z ∈ D ×ˢ Icc (a / 2) (p - a / 2) :=
    ⟨hz.1, by rw [ht]; exact hgap.le, by rw [ht]⟩
  have hsame : P.map (periodUpperCoordinates a p z) = u z :=
    (P.periodCutMap_upper hgap u hz.2.1).symm.trans
      (P.periodCutMap_middle ha hgap u hlower hupper hzM)
  exact P.middlePiece_injective H u hvalue hzM hw (hsame.symm.trans heq)

end PoincareConjecture.M76.OriginalDiskProduct
