import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoProperArcCuts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalStripDiskAttachment










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)



theorem strip_center_is_proper_arc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q : Set E} (c : P2 → E)
    (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hcS : MapsTo c source S)
    (hcQ : ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1) :
    IsFinitePLBallPair ℝ (c '' arm 0) {c (0, 0), c (1, 0)} ∧
      c (0, 0) ∈ Q ∧ c (1, 0) ∈ Q ∧ c (0, 0) ≠ c (1, 0) ∧
      (c '' arm 0) \ {c (0, 0), c (1, 0)} ⊆ S \ Q := by
  have hcenter : arm 0 ⊆ source := by
    rintro x ⟨hx, hx0⟩
    exact ⟨hx, by simp only [mem_singleton_iff] at hx0; rw [hx0]; norm_num⟩
  have h0 : ((0, 0) : P2) ∈ source := by norm_num [source]
  have h1 : ((1, 0) : P2) ∈ source := by norm_num [source]
  have hball := (exists_arm_parameter 0).1.image_of_subset hcPL hcenter hci
  rw [image_pair] at hball
  refine ⟨hball, (hcQ _ h0).mpr (Or.inl rfl), (hcQ _ h1).mpr (Or.inr rfl), ?_, ?_⟩
  · intro h
    have h01 : (0 : ℝ) = 1 := congrArg Prod.fst (hci h0 h1 h)
    norm_num at h01
  · rintro y ⟨⟨x, hx, rfl⟩, hnot⟩
    refine ⟨hcS (hcenter hx), ?_⟩
    intro hxQ
    have hx0 : x.2 = 0 := hx.2
    rcases (hcQ x (hcenter hx)).mp hxQ with hleft | hright
    · have heq : x = (0, 0) := Prod.ext hleft hx0
      exact hnot (by simp only [heq, mem_insert_iff, mem_singleton_iff, true_or])
    · have heq : x = (1, 0) := Prod.ext hright hx0
      exact hnot (by simp only [heq, mem_insert_iff, mem_singleton_iff, or_true])




theorem exists_three_disks_of_disjoint_strips
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q : Set E} (hS : IsFinitePLBallPair P2 S Q) (c0 c1 : P2 → E)
    (hc0PL : FinitePiecewiseAffineOn c0 source)
    (hc1PL : FinitePiecewiseAffineOn c1 source)
    (hc0i : InjOn c0 source) (hc1i : InjOn c1 source)
    (hc0S : MapsTo c0 source S) (hc1S : MapsTo c1 source S)
    (hc0Q : ∀ x ∈ source, c0 x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (hc1Q : ∀ x ∈ source, c1 x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (hdisj : Disjoint (c0 '' source) (c1 '' source)) :
    let W := c0 '' arm 0
    let Z := c1 '' arm 0
    ∃ A M C : Set E,
      IsFinitePLBallPair P2 A ((A ∩ Q) ∪ W) ∧
      IsFinitePLBallPair P2 M (((M ∩ Q) ∪ W) ∪ Z) ∧
      IsFinitePLBallPair P2 C ((C ∩ Q) ∪ Z) ∧
      (A ∪ M) ∪ C = S ∧ A ∩ M = W ∧ M ∩ C = Z ∧ Disjoint A C := by
  obtain ⟨hW, ha, hb, hab, hproperW⟩ :=
    strip_center_is_proper_arc c0 hc0PL hc0i hc0S hc0Q
  obtain ⟨hZ, hc, hd, hcd, hproperZ⟩ :=
    strip_center_is_proper_arc c1 hc1PL hc1i hc1S hc1Q
  have hcenter : arm 0 ⊆ source := by
    rintro x ⟨hx, hx0⟩
    exact ⟨hx, by simp only [mem_singleton_iff] at hx0; rw [hx0]; norm_num⟩
  exact exists_two_proper_arc_cuts hS hW hZ ha hb hc hd hab hcd
    (hdisj.mono (image_mono hcenter) (image_mono hcenter)) hproperW hproperZ

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
