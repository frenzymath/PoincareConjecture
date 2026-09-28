import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoCoverCoordinates










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexTwoStandard

local notation "W" => ((Fin 2 ⊕ Fin 1) → ℝ)
local notation "V" => (Fin 3 → ℝ)
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 2 ↪ Fin 2 ⊕ Fin 1)
local notation "D" => coordinateCylinder J
local notation "D3" => coordinateCylinder ({0, 1} : Finset (Fin 3))

private theorem coordinates_preimage_cylinder : coverCoordinates ⁻¹' D3 = D := by
  ext x
  exact (coverCoordinates_mem_cylinder x).symm

private theorem coordinates_preimage_frontier :
    coverCoordinates ⁻¹' frontier D3 = frontier D := by
  change coverCoordinates.toHomeomorph ⁻¹' frontier D3 = frontier D
  rw [coverCoordinates.toHomeomorph.preimage_frontier]
  exact congrArg frontier coordinates_preimage_cylinder




theorem cover_conjugate_conditions
    (A : W ≃ₜ W) (hAout : ∀ x : W, 2 ≤ ‖x‖ → A x = x)
    (hArel : EqOn A id (Dᶜ ∪ frontier D)) (P : Set W) :
    let A3 := coverCoordinates.symm.toHomeomorph.trans
      (A.trans coverCoordinates.toHomeomorph)
    (∀ x : V, 2 ≤ ‖x‖ → A3 x = x) ∧
      EqOn A3 id (D3ᶜ ∪ frontier D3) ∧
      A3 '' (coverCoordinates '' P) = coverCoordinates '' (A '' P) := by
  dsimp only
  have hnorm (x : V) : ‖coverCoordinates.symm x‖ = ‖x‖ := by
    have hh := coverCoordinates_norm (coverCoordinates.symm x)
    rw [coverCoordinates.apply_symm_apply] at hh
    exact hh.symm
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change coverCoordinates (A (coverCoordinates.symm x)) = x
    rw [hAout _ (by rwa [hnorm]), coverCoordinates.apply_symm_apply]
  · intro x hx
    have hm : coverCoordinates.symm x ∈ Dᶜ ∪ frontier D := by
      rcases hx with hx | hx
      · left
        intro hy
        have hh := (coverCoordinates_mem_cylinder _).mp hy
        rw [coverCoordinates.apply_symm_apply] at hh
        exact hx hh
      · right
        rw [← coordinates_preimage_frontier]
        change coverCoordinates (coverCoordinates.symm x) ∈ frontier D3
        rwa [coverCoordinates.apply_symm_apply]
    change coverCoordinates (A (coverCoordinates.symm x)) = x
    rw [hArel hm, id_eq, coverCoordinates.apply_symm_apply]
  · ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change coverCoordinates (A (coverCoordinates.symm (coverCoordinates x))) ∈ _
      rw [coverCoordinates.symm_apply_apply]
      exact mem_image_of_mem coverCoordinates (mem_image_of_mem A hx)
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨coverCoordinates x, mem_image_of_mem coverCoordinates hx, ?_⟩
      change coverCoordinates (A (coverCoordinates.symm (coverCoordinates x))) = _
      rw [coverCoordinates.symm_apply_apply]




theorem exists_cover_supported_placement
    (P : Set W) (A : W ≃ₜ W)
    (Q : V ≃ₜ V)
    (hQPL : FinitePiecewiseAffineOn Q (closedBall (0 : V) 1))
    (hQout : ∀ x : V, 2 ≤ ‖x‖ → Q x = x)
    (hQrel : EqOn Q id (D3ᶜ ∪ frontier D3))
    (hplace : MapsTo Q (closedBall (0 : V) 1) (coverCoordinates '' (A '' P))) :
    ∃ B : W ≃ₜ W,
      FinitePiecewiseAffineOn B (closedBall (0 : W) 1) ∧
      (∀ x : W, 2 ≤ ‖x‖ → B x = x) ∧
      EqOn B id (Dᶜ ∪ frontier D) ∧
      MapsTo B (closedBall (0 : W) 1) (A '' P) := by
  let B := coverCoordinates.toHomeomorph.trans
    (Q.trans coverCoordinates.symm.toHomeomorph)
  have hball : coverCoordinates.symm '' closedBall (0 : V) 1 =
      closedBall (0 : W) 1 := by
    rw [← coverCoordinates_closedBall 1, image_image]
    simp only [ContinuousAffineEquiv.symm_apply_apply, image_id']
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · have hh := (hQPL.precomp_affineEquiv coverCoordinates).postcomp
      coverCoordinates.symm.toContinuousAffineMap
    rw [hball] at hh
    exact hh
  · intro x hx
    change coverCoordinates.symm (Q (coverCoordinates x)) = x
    rw [hQout _ (by rwa [coverCoordinates_norm]), coverCoordinates.symm_apply_apply]
  · intro x hx
    have hm : coverCoordinates x ∈ D3ᶜ ∪ frontier D3 := by
      rcases hx with hx | hx
      · exact Or.inl (fun hy => hx ((coverCoordinates_mem_cylinder x).mpr hy))
      · right
        have hh : x ∈ coverCoordinates ⁻¹' frontier D3 :=
          coordinates_preimage_frontier.symm ▸ hx
        exact hh
    change coverCoordinates.symm (Q (coverCoordinates x)) = x
    rw [hQrel hm, id_eq, coverCoordinates.symm_apply_apply]
  · intro x hx
    have hcx : coverCoordinates x ∈ closedBall (0 : V) 1 := by
      simpa only [mem_closedBall_zero_iff, coverCoordinates_norm] using hx
    obtain ⟨y, hy, heq⟩ := hplace hcx
    change coverCoordinates.symm (Q (coverCoordinates x)) ∈ A '' P
    rw [← heq, coverCoordinates.symm_apply_apply]
    exact hy

end PoincareConjecture.M76.HamiltonIndexTwoStandard
