import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripArmCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Mathlib.TubeArmOrientation

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

def stripEnds : Set P2 := ({0, 1} : Set ℝ) ×ˢ Icc (-1 : ℝ) 1

theorem stripEnds_subset_source : stripEnds ⊆ source := by
  rintro x ⟨hx, hu⟩
  rcases hx with hx | hx
  · exact ⟨by rw [hx]; norm_num, hu⟩
  · exact ⟨by rw [hx]; norm_num, hu⟩

theorem stripRim_eq_ends_union_arms : stripRim = (stripEnds ∪ arm (-1)) ∪ arm 1 := by
  ext x
  simp only [stripRim, stripEnds, arm, mem_union, mem_prod,
    mem_insert_iff, mem_singleton_iff]
  tauto

theorem resolutionMap_mapsTo_tube {b : ℝ} (hb : b ≤ 1) (alternatePair positive : Bool) :
    MapsTo (resolutionMap b alternatePair positive) source tube := by
  cases alternatePair
  · exact (mapsTo_tube hb positive).1
  · exact (mapsTo_tube hb positive).2

theorem resolutionMap_longitudinal (b : ℝ) (alternatePair positive : Bool) (p : P2) :
    (resolutionMap b alternatePair positive p).2 = p.1 := by
  cases alternatePair <;> rfl

theorem reoriented_tube_frontier_iff
    {X : Type*} {F : Set X} (τ : C3 → X)
    (hτF : ∀ z ∈ tube, τ z ∈ F ↔ z.2 = 0 ∨ z.2 = 1)
    (s0 s1 : Bool) (z : C3) (hz : z ∈ tube) :
    (τ ∘ tubeArmOrientation s0 s1) z ∈ F ↔ z.2 = 0 ∨ z.2 = 1 := by
  have h := hτF _ ((tubeArmOrientation_mem_tube s0 s1 z).mpr hz)
  rwa [tubeArmOrientation_longitudinal] at h

theorem reoriented_tube_marked_ends
    {X : Type*} {Fmark : Set X} (τ : C3 → X)
    (hτmark : ∀ z ∈ tube, z.2 = 0 ∨ z.2 = 1 → τ z ∈ Fmark)
    (s0 s1 : Bool) (z : C3) (hz : z ∈ tube) (ht : z.2 = 0 ∨ z.2 = 1) :
    (τ ∘ tubeArmOrientation s0 s1) z ∈ Fmark := by
  apply hτmark _ ((tubeArmOrientation_mem_tube s0 s1 z).mpr hz)
  simpa only [tubeArmOrientation_longitudinal] using ht

theorem resolution_strip_frontier_preimage
    {X : Type*} {F : Set X} (τ : C3 → X)
    (hτF : ∀ z ∈ tube, τ z ∈ F ↔ z.2 = 0 ∨ z.2 = 1)
    {b : ℝ} (hb : b ≤ 1) (alternatePair positive : Bool) :
    source ∩ (τ ∘ resolutionMap b alternatePair positive) ⁻¹' F = stripEnds := by
  ext p
  constructor
  · rintro ⟨hp, hF⟩
    have ht := (hτF _ (resolutionMap_mapsTo_tube hb alternatePair positive hp)).mp hF
    rw [resolutionMap_longitudinal] at ht
    exact ⟨ht, hp.2⟩
  · intro hp
    have hpS := stripEnds_subset_source hp
    refine ⟨hpS, (hτF _ (resolutionMap_mapsTo_tube hb alternatePair positive hpS)).mpr ?_⟩
    simpa only [resolutionMap_longitudinal, mem_insert_iff, mem_singleton_iff] using hp.1

theorem resolution_strip_ends_in_mark
    {X : Type*} {Fmark : Set X} (τ : C3 → X)
    (hτmark : ∀ z ∈ tube, z.2 = 0 ∨ z.2 = 1 → τ z ∈ Fmark)
    {b : ℝ} (hb : b ≤ 1) (alternatePair positive : Bool) :
    MapsTo (τ ∘ resolutionMap b alternatePair positive) stripEnds Fmark := by
  intro p hp
  apply hτmark _ (resolutionMap_mapsTo_tube hb alternatePair positive (stripEnds_subset_source hp))
  simpa only [resolutionMap_longitudinal, mem_insert_iff, mem_singleton_iff] using hp.1

theorem resolution_strip_arm_frontier_inter
    {X : Type*} {F : Set X} (τ : C3 → X)
    (hτF : ∀ z ∈ tube, τ z ∈ F ↔ z.2 = 0 ∨ z.2 = 1)
    {b u : ℝ} (hb : b ≤ 1) (hu : u ∈ Icc (-1 : ℝ) 1)
    (alternatePair positive : Bool) :
    arm u ∩ (τ ∘ resolutionMap b alternatePair positive) ⁻¹' F = {(0, u), (1, u)} := by
  have hQ (x : P2) (hx : x ∈ source) :
      id x ∈ (τ ∘ resolutionMap b alternatePair positive) ⁻¹' F ↔ x.1 = 0 ∨ x.1 = 1 := by
    have h := hτF _ (resolutionMap_mapsTo_tube hb alternatePair positive hx)
    simpa only [resolutionMap_longitudinal, mem_preimage, id_eq, Function.comp_apply] using h
  simpa only [id_eq, image_id'] using embedded_strip_arm_inter_old_rim id hQ u hu

theorem retained_piece_frontier_preimage
    {E X : Type*} {S Q A : Set E} {F : Set X} (f : E → X)
    (hf : ∀ x ∈ S, f x ∈ F ↔ x ∈ Q) (hAS : A ⊆ S) :
    A ∩ f ⁻¹' F = A ∩ Q := by
  ext x
  exact and_congr_right fun hx ↦ hf x (hAS hx)

theorem original_strip_arm_frontier_inter
    {E X : Type*} {S Q : Set E} {F : Set X} (f : E → X) (c : P2 → E)
    (hf : ∀ x ∈ S, f x ∈ F ↔ x ∈ Q) (hcS : MapsTo c source S)
    (hcQ : ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (c '' arm u) ∩ f ⁻¹' F = {c (0, u), c (1, u)} := by
  apply embedded_strip_arm_inter_old_rim c _ u hu
  intro x hx
  exact (hf (c x) (hcS hx)).trans (hcQ x hx)

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
