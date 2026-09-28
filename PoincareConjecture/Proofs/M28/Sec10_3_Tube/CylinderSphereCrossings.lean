import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereOrder










set_option autoImplicit false

open Set
open scoped Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]




theorem exists_sphere_crossing_of_signed_height
    {U S : Set M} {h : M → ℝ} (hh : ContinuousOn h U)
    (hzero : ∀ x ∈ U, h x = 0 ↔ x ∈ S)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hγU : MapsTo γ (Icc a b) U)
    (ha : h (γ a) < 0) (hb : 0 < h (γ b)) :
    ∃ t ∈ Ioo a b, γ t ∈ S := by
  have hheight : ContinuousOn (fun t => h (γ t)) (Icc a b) := hh.comp hγ hγU
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hab hheight ⟨ha.le, hb.le⟩
  have hat : a < t := lt_of_le_of_ne ht.1 (by
    intro he
    subst t
    exact (ne_of_lt ha) heq)
  have htb : t < b := lt_of_le_of_ne ht.2 (by
    intro he
    subst t
    exact (ne_of_gt hb) heq)
  exact ⟨t, ⟨hat, htb⟩, (hzero (γ t) (hγU ht)).mp heq⟩



theorem exists_sphere_return_after_negative_height
    {U S : Set M} {h : M → ℝ} (hh : ContinuousOn h U)
    (hzero : ∀ x ∈ U, h x = 0 ↔ x ∈ S)
    {γ : ℝ → M} {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hγU : MapsTo γ (Icc a b) U)
    (ht : h (γ t) < 0) (hb : 0 < h (γ b)) :
    ∃ d ∈ Ioo t b, γ d ∈ S := by
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc hat le_rfl
  exact exists_sphere_crossing_of_signed_height hh hzero htb
    (hγ.mono hsub) (fun _ hs => hγU (hsub hs)) ht hb



theorem exists_sphere_hit_before_positive_height
    {U S : Set M} {h : M → ℝ} (hh : ContinuousOn h U)
    (hzero : ∀ x ∈ U, h x = 0 ↔ x ∈ S)
    {γ : ℝ → M} {a t b : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hγU : MapsTo γ (Icc a b) U)
    (ha : h (γ a) < 0) (ht : 0 < h (γ t)) :
    ∃ c ∈ Ioo a t, γ c ∈ S := by
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl htb
  exact exists_sphere_crossing_of_signed_height hh hzero hat
    (hγ.mono hsub) (fun _ hs => hγU (hsub hs)) ha ht

end PoincareConjecture.M28
