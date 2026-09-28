import PoincareConjecture.Proofs.M76.Rigidity.OriginalPeriodMap
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut









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



theorem image_periodCutMap (P : OriginalDiskProduct e R j)
    {a p : ℝ} (ha : 0 < a) (hgap : a / 2 < p - a / 2)
    (H : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E) ≃ₜ P.cutCarrier)
    (u : E → X)
    (hvalue : ∀ z : (D ×ˢ Icc (a / 2) (p - a / 2) : Set E), u z = (H z : X))
    (hlower : ∀ z ∈ D, u (z, a / 2) = P.map (z, 1 / 2))
    (hupper : ∀ z ∈ D, u (z, p - a / 2) = P.map (z, -(1 / 2)))
    (hcover : P.closedStrip ∪ P.cutCarrier = R) :
    P.periodCutMap a p u '' (D ×ˢ Icc 0 p) = R := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    by_cases hlo : z.2 ≤ a / 2
    · rw [P.periodCutMap_lower a p u hlo]
      have hc := periodLowerCoordinates_mapsTo ha ⟨hz.1, hz.2.1, hlo⟩
      exact P.inside ⟨hc.1, by linarith [hc.2.1], by linarith [hc.2.2]⟩
    · by_cases hup : p - a / 2 ≤ z.2
      · rw [P.periodCutMap_upper hgap u hup]
        have hc := periodUpperCoordinates_mapsTo ha ⟨hz.1, hup, hz.2.2⟩
        exact P.inside ⟨hc.1, by linarith [hc.2.1], by linarith [hc.2.2]⟩
      · have hm : z ∈ D ×ˢ Icc (a / 2) (p - a / 2) :=
          ⟨hz.1, (not_le.mp hlo).le, (not_le.mp hup).le⟩
        rw [P.periodCutMap_middle ha hgap u hlower hupper hm, hvalue ⟨z, hm⟩]
        exact (H ⟨z, hm⟩).property.1
  · intro hx
    rcases hcover.symm.subset hx with hstrip | hcut
    · obtain ⟨z, hz, rfl⟩ := hstrip
      by_cases hnonneg : 0 ≤ z.2
      · have ht : a * z.2 ∈ Icc (0 : ℝ) (a / 2) :=
          ⟨mul_nonneg ha.le hnonneg, by nlinarith [hz.2.2]⟩
        refine ⟨(z.1, a * z.2), ⟨hz.1, ht.1, by linarith [ht.2]⟩, ?_⟩
        rw [P.periodCutMap_lower a p u ht.2, periodLowerCoordinates_mul ha.ne']
      · have ht : p + a * z.2 ∈ Icc (p - a / 2) p :=
          ⟨by nlinarith [hz.2.1], by nlinarith [lt_of_not_ge hnonneg]⟩
        refine ⟨(z.1, p + a * z.2), ⟨hz.1, by linarith [ht.1], ht.2⟩, ?_⟩
        rw [P.periodCutMap_upper hgap u ht.1, periodUpperCoordinates_add_mul ha.ne']
    · let z := H.symm ⟨x, hcut⟩
      have hz : (z : E) ∈ D ×ˢ Icc (a / 2) (p - a / 2) := z.property
      refine ⟨z, ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩, ?_⟩
      rw [P.periodCutMap_middle ha hgap u hlower hupper hz, hvalue z]
      exact congrArg Subtype.val (H.apply_symm_apply ⟨x, hcut⟩)

end PoincareConjecture.M76.OriginalDiskProduct
