import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneBlockPlacement
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneProtectedImage

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V" => ((Fin 1 ⊕ Fin 2) → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "J" => Finset.univ.map (Function.Embedding.inl : Fin 1 ↪ Fin 1 ⊕ Fin 2)
local notation "D" => coordinateCylinder J

theorem exists_cover_supported_block_placement
    (P : Set V) (A : V ≃ₜ V) (Q : W ≃ₜ W)
    (hQ : FinitePiecewiseAffineOn Q squareBlock)
    (hplace : Q '' squareMiddleBlock = coverCoordinates '' (A '' P))
    (hfix : EqOn Q id (interior squareBlock)ᶜ) :
    ∃ B : V ≃ₜ V,
      FinitePiecewiseAffineOn B (closedBall (0 : V) 1) ∧
      (∀ x : V, 2 ≤ ‖x‖ → B x = x) ∧
      EqOn B id (Dᶜ ∪ frontier D) ∧
      MapsTo B (closedBall (0 : V) 1) (A '' P) := by
  let B := coverCoordinates.toHomeomorph.trans
    (Q.trans coverCoordinates.symm.toHomeomorph)
  have hunit (x : V) (hx : x ∈ closedBall (0 : V) 1) :
      coverCoordinates x ∈ squareMiddleBlock := by
    have h := coverCoordinates_unit.subset (mem_image_of_mem coverCoordinates hx)
    exact ⟨h.1, mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp h.2).trans (by norm_num))⟩
  have hunitBlock (x : V) (hx : x ∈ closedBall (0 : V) 1) :
      coverCoordinates x ∈ squareBlock := by
    have h := hunit x hx
    exact ⟨h.1, mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp h.2).trans (by norm_num))⟩
  have hpre : coverCoordinates.symm '' squareBlock =
      coverCoordinates ⁻¹' squareBlock := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change coverCoordinates (coverCoordinates.symm y) ∈ squareBlock
      rwa [coverCoordinates.apply_symm_apply]
    · intro hx
      exact ⟨coverCoordinates x, hx, coverCoordinates.symm_apply_apply x⟩
  have hC : coverCoordinates ⁻¹' squareBlock ⊆ D := by
    intro x hx i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    have hj : j = 0 := Subsingleton.elim _ _
    rw [hj]
    exact abs_le.mpr hx.1
  have hinterior (x : V) (hx : coverCoordinates x ∈ interior squareBlock) :
      x ∈ interior D := by
    apply interior_mono hC
    change x ∈ interior (coverCoordinates.toHomeomorph ⁻¹' squareBlock)
    rw [← coverCoordinates.toHomeomorph.preimage_interior]
    exact hx
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · have hfull := (hQ.precomp_affineEquiv coverCoordinates).postcomp
      coverCoordinates.symm.toContinuousAffineMap
    rw [hpre] at hfull
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_unit_cube (ι := Fin 1 ⊕ Fin 2)
    have hh := hfull.restrict K hK (fun x hx => hunitBlock x (hKs.subset hx))
    rwa [hKs] at hh
  · intro x hx
    have hout : coverCoordinates x ∉ interior squareBlock := by
      intro hi
      rw [squareBlock, interior_prod_eq, interior_Icc,
        interior_closedBall _ (by norm_num)] at hi
      have hn : ‖coverCoordinates x‖ < 2 := by
        rw [Prod.norm_def, max_lt_iff, Real.norm_eq_abs]
        exact ⟨(abs_lt.mpr hi.1).trans (by norm_num), mem_ball_zero_iff.mp hi.2⟩
      rw [coverCoordinates_norm] at hn
      exact (not_lt_of_ge hx) hn
    change coverCoordinates.symm (Q (coverCoordinates x)) = x
    rw [hfix hout, id_eq, coverCoordinates.symm_apply_apply]
  · intro x hx
    have hout : coverCoordinates x ∉ interior squareBlock := by
      intro hi
      rcases hx with hx | hx
      · exact hx (interior_subset (hinterior x hi))
      · exact hx.2 (hinterior x hi)
    change coverCoordinates.symm (Q (coverCoordinates x)) = x
    rw [hfix hout, id_eq, coverCoordinates.symm_apply_apply]
  · intro x hx
    have h : Q (coverCoordinates x) ∈ coverCoordinates '' (A '' P) :=
      hplace.subset (mem_image_of_mem Q (hunit x hx))
    obtain ⟨y, hy, heq⟩ := h
    change coverCoordinates.symm (Q (coverCoordinates x)) ∈ A '' P
    rw [← heq, coverCoordinates.symm_apply_apply]
    exact hy

end PoincareConjecture.M76.HamiltonIndexOne
