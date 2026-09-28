import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripHalfDiskComplement

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1

theorem exists_embedded_strip_arm_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (c : P2 → E) (hcPL : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    IsFinitePLBallPair ℝ (c '' arm u) {c (0, u), c (1, u)} ∧
      c (0, u) ≠ c (1, u) ∧
      ∃ p : I01 ≃ₜ (c '' arm u), p.IsFinitePL ∧
        ∀ t : I01, (p t : E) = c ((t : ℝ), u) := by
  have hsub : arm u ⊆ source := fun x hx => ⟨hx.1, hx.2.symm ▸ hu⟩
  obtain ⟨hW, q, hq, hqval⟩ := exists_arm_parameter u
  have hball : IsFinitePLBallPair ℝ (c '' arm u) {c (0, u), c (1, u)} := by
    simpa only [image_pair] using hW.image_of_subset hcPL hsub hci
  have hends : c (0, u) ≠ c (1, u) := by
    intro h
    have heq := hci (show (0, u) ∈ source from ⟨by norm_num, hu⟩)
      (show (1, u) ∈ source from ⟨by norm_num, hu⟩) h
    have h01 := congrArg Prod.fst heq
    norm_num at h01
  have hcopy := hW
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
  have hcW : FinitePiecewiseAffineOn c (arm u) := by
    rw [← hKs]
    exact hcPL.restrict K hK (hKs.subset.trans hsub)
  obtain ⟨j, hj, hjval⟩ := hcW.exists_homeomorph_image (hci.mono hsub)
  refine ⟨hball, hends, q.trans j, hq.trans hj, ?_⟩
  intro t
  exact (hjval (q t)).trans (congrArg c (hqval t))

theorem embedded_strip_arm_inter_old_rim
    {E : Type*} {Q : Set E} (c : P2 → E)
    (hcQ : ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1)
    (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (c '' arm u) ∩ Q = {c (0, u), c (1, u)} := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hxQ⟩
    have hxS : x ∈ source := ⟨hx.1, hx.2.symm ▸ hu⟩
    rcases (hcQ x hxS).mp hxQ with h0 | h1
    · exact Or.inl (congrArg c (Prod.ext h0 hx.2))
    · exact Or.inr (congrArg c (Prod.ext h1 hx.2))
  · rintro (rfl | rfl)
    · exact ⟨⟨(0, u), ⟨by norm_num, rfl⟩, rfl⟩,
        (hcQ (0, u) ⟨by norm_num, hu⟩).mpr (Or.inl rfl)⟩
    · exact ⟨⟨(1, u), ⟨by norm_num, rfl⟩, rfl⟩,
        (hcQ (1, u) ⟨by norm_num, hu⟩).mpr (Or.inr rfl)⟩

theorem outer_disk_old_rim_is_interval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A Q W : Set E} {a b : E}
    (hA : IsFinitePLBallPair P2 A ((A ∩ Q) ∪ W))
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a ≠ b)
    (hWQ : W ∩ Q = {a, b}) :
    IsFinitePLBallPair ℝ (A ∩ Q) {a, b} := by
  obtain ⟨V, hV, hcover, hinter⟩ :=
    hA.exists_boundary_arc_complement hW subset_union_right hab
  have hVA : V ⊆ A := (subset_union_right.trans hcover.subset).trans hA.1
  have hVeq : V = A ∩ Q := by
    apply Subset.antisymm
    · intro x hxV
      rcases hcover.subset (Or.inr hxV) with hxQ | hxW
      · exact hxQ
      · exact ⟨hVA hxV, (hWQ.symm.subset (hinter.subset ⟨hxW, hxV⟩)).2⟩
    · intro x hxQ
      rcases hcover.symm.subset (Or.inl hxQ) with hxW | hxV
      · exact (hinter.symm.subset (hWQ.subset ⟨hxW, hxQ.2⟩)).2
      · exact hxV
  exact hVeq ▸ hV

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
