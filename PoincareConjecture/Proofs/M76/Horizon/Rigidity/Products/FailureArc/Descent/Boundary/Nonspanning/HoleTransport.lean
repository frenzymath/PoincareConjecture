import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInterior
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_inner_disk_image
    {S T D : Set P2} (e : S ≃ₜ T) (he : e.IsFinitePL)
    (hD : IsFinitePLBallPair P2 D (frontier D)) (hDS : D ⊆ interior S) :
    ∃ (P : Set P2) (q : D ≃ₜ P),
      q.IsFinitePL ∧ IsFinitePLBallPair P2 P (frontier P) ∧ P ⊆ interior T ∧
      (∀ x : D, (q x : P2) = e ⟨x, interior_subset (hDS x.property)⟩) ∧
      (∀ x : S, (e x : P2) ∈ P ↔ (x : P2) ∈ D) ∧
      (∀ x : S, (e x : P2) ∈ interior P ↔ (x : P2) ∈ interior D) ∧
      ∀ x : S, (e x : P2) ∈ frontier P ↔ (x : P2) ∈ frontier D := by
  obtain ⟨f, hf, hval⟩ := he
  have hfi : InjOn f S := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (show e ⟨x, hx⟩ = e ⟨y, hy⟩ from
      Subtype.ext ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  have hsub : D ⊆ S := hDS.trans interior_subset
  have hDcopy := hD
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hDcopy
  have hfD : FinitePiecewiseAffineOn f D := by
    rw [← hKs]
    exact hf.restrict K hK (hKs.subset.trans hsub)
  obtain ⟨q, hq, hqval⟩ := hfD.exists_homeomorph_image (hfi.mono hsub)
  have hP := hD.image hfD (hfi.mono hsub)
  have hPf : IsFinitePLBallPair P2 (f '' D) (frontier (f '' D)) :=
    (hP.frontier_eq_of_finrank_eq rfl).symm ▸ hP
  have hmem (B : Set P2) (hBS : B ⊆ S) (x : S) :
      (e x : P2) ∈ f '' B ↔ (x : P2) ∈ B := by
    rw [hval]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact hfi (hBS hy) x.property hxy ▸ hy
    · intro hx
      exact mem_image_of_mem f hx
  have hfront (x : S) :
      (e x : P2) ∈ frontier (f '' D) ↔ (x : P2) ∈ frontier D := by
    rw [hP.frontier_eq_of_finrank_eq rfl]
    exact hmem (frontier D) (hD.1.trans hsub) x
  refine ⟨f '' D, q, hq, hPf, ?_, ?_, hmem D hsub, ?_, hfront⟩
  · rintro z ⟨x, hx, rfl⟩
    rw [← hval ⟨x, hsub hx⟩]
    exact (show e.IsFinitePL from ⟨f, hf, hval⟩).mem_interior rfl (hDS hx)
  · intro x
    exact (hqval x).trans (hval ⟨x, hsub x.property⟩).symm
  · intro x
    rw [hPf.interior_eq_sdiff_of_finrank_eq rfl, hD.interior_eq_sdiff_of_finrank_eq rfl]
    exact and_congr (hmem D hsub x) (not_congr (hfront x))

end PoincareConjecture.M76.Dehn
