import PoincareConjecture.Proofs.M76.Rigidity.OriginalStripBoundaryTrace
import PoincareConjecture.Proofs.M76.Rigidity.SourceComplementCylinder









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

variable {ι : Type*} {e : ι → OpenPartialHomeomorph X V3} {j : V2 → X}
  (P : OriginalDiskProduct e R j) {a : ℝ}



theorem marked_meridian_strip_trace (ha : 0 < a)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t)) :
    frontier R ∩ P.openStrip =
      hamiltonMeridianCutAmbientMap '' (Q ×ˢ Ioo (-(a / 2)) (a / 2)) := by
  rw [P.frontier_inter_openStrip]
  have hI : Ioo (-(1 / 2 : ℝ)) (1 / 2) ⊆ I :=
    fun _ ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z.1, a * z.2), ⟨hz.1, ?_, ?_⟩, (hmark _ hz.1 _ (hI hz.2)).symm⟩
    · nlinarith [mul_lt_mul_of_pos_left hz.2.1 ha]
    · nlinarith [mul_lt_mul_of_pos_left hz.2.2 ha]
  · rintro ⟨z, hz, rfl⟩
    have ht : z.2 / a ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      constructor
      · apply (lt_div_iff₀ ha).mpr
        linarith [hz.2.1]
      · apply (div_lt_iff₀ ha).mpr
        linarith [hz.2.2]
    refine ⟨(z.1, z.2 / a), ⟨hz.1, ht⟩, ?_⟩
    rw [hmark _ hz.1 _ (hI ht), mul_div_cancel₀ _ ha.ne']




theorem marked_meridian_cap_rims
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t)) :
    (∀ z ∈ Q, P.map (z, (1 / 2 : ℝ)) =
      hamiltonMeridianCutAmbientMap (z, a / 2)) ∧
    (∀ z ∈ Q, P.map (z, -(1 / 2 : ℝ)) =
      hamiltonMeridianCutAmbientMap (z, p - a / 2)) := by
  constructor
  · intro z hz
    simpa only [mul_one_div] using hmark z hz (1 / 2) (by norm_num)
  · intro z hz
    rw [hamiltonComplementCylinder_upper]
    simpa only [mul_neg, mul_one_div] using hmark z hz (-(1 / 2)) (by norm_num)



theorem marked_meridian_retained_frontier (ha : 0 < a) (ha_small : a ≤ 1 / 2)
    (hmark : ∀ z ∈ Q, ∀ t ∈ I,
      P.map (z, t) = hamiltonMeridianCutAmbientMap (z, a * t)) :
    hamiltonMeridianCutAmbientMap '' (Q ×ˢ Icc (a / 2) (p - a / 2)) =
      frontier R \ P.openStrip := by
  rw [image_hamiltonComplementCylinder (by linarith : 0 < a / 2)
    (by norm_num at ha_small ⊢; linarith : a / 2 < p / 2)]
  rw [← P.marked_meridian_strip_trace ha hmark]
  ext y
  simp only [mem_sdiff, mem_inter_iff]
  tauto

end PoincareConjecture.M76.OriginalDiskProduct
