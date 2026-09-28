import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodOuterFibers
import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodMiddleFibers









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}



theorem periodCutMap_eq_iff (P : OriginalDiskProduct e R j)
    {a p : ℝ} (ha : 0 < a) (hgap : a / 2 < p - a / 2)
    (H : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E) ≃ₜ P.cutCarrier)
    (u : E → X)
    (hvalue : ∀ z : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E), u z = (H z : X))
    (hlower : ∀ z ∈ D, u (z, a / 2) = P.map (z, 1 / 2))
    (hupper : ∀ z ∈ D, u (z, p - a / 2) = P.map (z, -(1 / 2)))
    {z w : E} (hz : z ∈ D ×ˢ Icc 0 p) (hw : w ∈ D ×ˢ Icc 0 p) :
    P.periodCutMap a p u z = P.periodCutMap a p u w ↔
      z.1 = w.1 ∧ (z.2 = w.2 ∨ (z.2 = 0 ∧ w.2 = p) ∨ (z.2 = p ∧ w.2 = 0)) := by
  have hdiag : z = w →
      z.1 = w.1 ∧ (z.2 = w.2 ∨ (z.2 = 0 ∧ w.2 = p) ∨ (z.2 = p ∧ w.2 = 0)) := by
    rintro rfl
    exact ⟨rfl, Or.inl rfl⟩
  constructor
  · intro heq
    by_cases hzl : z.2 ≤ a / 2
    · have hz0 : z ∈ D ×ˢ Icc 0 (a / 2) := ⟨hz.1, hz.2.1, hzl⟩
      rw [P.periodCutMap_lower a p u hzl] at heq
      by_cases hwl : w.2 ≤ a / 2
      · have hw0 : w ∈ D ×ˢ Icc 0 (a / 2) := ⟨hw.1, hw.2.1, hwl⟩
        rw [P.periodCutMap_lower a p u hwl] at heq
        exact hdiag (P.lowerPiece_injective ha hz0 hw0 heq)
      · by_cases hwu : p - a / 2 ≤ w.2
        · have hw2 : w ∈ D ×ˢ Icc (p - a / 2) p := ⟨hw.1, hwu, hw.2.2⟩
          rw [P.periodCutMap_upper hgap u hwu] at heq
          obtain ⟨hf, ht, hq⟩ := (P.lowerPiece_eq_upperPiece_iff ha hz0 hw2).mp heq
          exact ⟨hf, Or.inr (Or.inl ⟨ht, hq⟩)⟩
        · have hw1 : w ∈ D ×ˢ Icc (a / 2) (p - a / 2) :=
            ⟨hw.1, (not_le.mp hwl).le, (not_le.mp hwu).le⟩
          rw [P.periodCutMap_middle ha hgap u hlower hupper hw1] at heq
          exact hdiag (P.eq_of_lowerPiece_eq_middle ha hgap H u hvalue
            hlower hupper hz0 hw1 heq)
    · by_cases hzu : p - a / 2 ≤ z.2
      · have hz2 : z ∈ D ×ˢ Icc (p - a / 2) p := ⟨hz.1, hzu, hz.2.2⟩
        rw [P.periodCutMap_upper hgap u hzu] at heq
        by_cases hwl : w.2 ≤ a / 2
        · have hw0 : w ∈ D ×ˢ Icc 0 (a / 2) := ⟨hw.1, hw.2.1, hwl⟩
          rw [P.periodCutMap_lower a p u hwl] at heq
          obtain ⟨hf, ht, hq⟩ := (P.lowerPiece_eq_upperPiece_iff ha hw0 hz2).mp heq.symm
          exact ⟨hf.symm, Or.inr (Or.inr ⟨hq, ht⟩)⟩
        · by_cases hwu : p - a / 2 ≤ w.2
          · have hw2 : w ∈ D ×ˢ Icc (p - a / 2) p := ⟨hw.1, hwu, hw.2.2⟩
            rw [P.periodCutMap_upper hgap u hwu] at heq
            exact hdiag (P.upperPiece_injective ha hz2 hw2 heq)
          · have hw1 : w ∈ D ×ˢ Icc (a / 2) (p - a / 2) :=
              ⟨hw.1, (not_le.mp hwl).le, (not_le.mp hwu).le⟩
            rw [P.periodCutMap_middle ha hgap u hlower hupper hw1] at heq
            exact hdiag (P.eq_of_upperPiece_eq_middle ha hgap H u hvalue
              hlower hupper hz2 hw1 heq)
      · have hz1 : z ∈ D ×ˢ Icc (a / 2) (p - a / 2) :=
          ⟨hz.1, (not_le.mp hzl).le, (not_le.mp hzu).le⟩
        rw [P.periodCutMap_middle ha hgap u hlower hupper hz1] at heq
        by_cases hwl : w.2 ≤ a / 2
        · have hw0 : w ∈ D ×ˢ Icc 0 (a / 2) := ⟨hw.1, hw.2.1, hwl⟩
          rw [P.periodCutMap_lower a p u hwl] at heq
          exact hdiag (P.eq_of_lowerPiece_eq_middle ha hgap H u hvalue
            hlower hupper hw0 hz1 heq.symm).symm
        · by_cases hwu : p - a / 2 ≤ w.2
          · have hw2 : w ∈ D ×ˢ Icc (p - a / 2) p := ⟨hw.1, hwu, hw.2.2⟩
            rw [P.periodCutMap_upper hgap u hwu] at heq
            exact hdiag (P.eq_of_upperPiece_eq_middle ha hgap H u hvalue
              hlower hupper hw2 hz1 heq.symm).symm
          · have hw1 : w ∈ D ×ˢ Icc (a / 2) (p - a / 2) :=
              ⟨hw.1, (not_le.mp hwl).le, (not_le.mp hwu).le⟩
            rw [P.periodCutMap_middle ha hgap u hlower hupper hw1] at heq
            exact hdiag (P.middlePiece_injective H u hvalue hz1 hw1 heq)
  · rintro ⟨hf, ht | ht | ht⟩
    · rw [Prod.ext hf ht]
    · have hz0 : z = (z.1, (0 : ℝ)) := Prod.ext rfl ht.1
      have hwp : w = (w.1, p) := Prod.ext rfl ht.2
      rw [hz0, hwp, (P.periodCutMap_endpoints ha hgap u z.1 hz.1).1,
        (P.periodCutMap_endpoints ha hgap u w.1 hw.1).2, hf]
    · have hzp : z = (z.1, p) := Prod.ext rfl ht.1
      have hw0 : w = (w.1, (0 : ℝ)) := Prod.ext rfl ht.2
      rw [hzp, hw0, (P.periodCutMap_endpoints ha hgap u z.1 hz.1).2,
        (P.periodCutMap_endpoints ha hgap u w.1 hw.1).1, hf]

end PoincareConjecture.M76.OriginalDiskProduct
