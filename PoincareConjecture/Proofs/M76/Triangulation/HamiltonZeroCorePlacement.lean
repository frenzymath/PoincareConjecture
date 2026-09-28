import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroCoreCompression
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroCorePointMove
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

theorem exists_hamilton_zero_core_placement {ι : Type*} [Fintype ι]
    (A : (ι → ℝ) ≃ₜ (ι → ℝ))
    (hA : ∀ x, 2 ≤ ‖x‖ → A x = x)
    (P : Set (ι → ℝ)) (hP : (0 : ι → ℝ) ∈ interior P) :
    ∃ Q : (ι → ℝ) ≃ₜ (ι → ℝ),
      FinitePiecewiseAffineOn Q (closedBall (0 : ι → ℝ) 1) ∧
      (∀ x, 2 ≤ ‖x‖ → Q x = x) ∧
      MapsTo Q (closedBall (0 : ι → ℝ) 1) (A '' P) := by
  have hA0 : ‖A (0 : ι → ℝ)‖ < 2 := by
    by_contra h
    have hn : 2 ≤ ‖A (0 : ι → ℝ)‖ := le_of_not_gt h
    have heq : A (0 : ι → ℝ) = 0 := A.injective (hA _ hn)
    simp only [heq, norm_zero] at hn
    norm_num at hn
  obtain ⟨M, hMPL, hM0, hMout⟩ := exists_supported_finitePL_cube_point_move (A 0) hA0
  let U : Set (ι → ℝ) := M ⁻¹' (A '' interior P)
  have hU : IsOpen U := (A.isOpenMap _ isOpen_interior).preimage M.continuous
  have h0U : (0 : ι → ℝ) ∈ U := by
    change M 0 ∈ A '' interior P
    rw [hM0]
    exact mem_image_of_mem A hP
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp hU 0 h0U
  obtain ⟨r, H, hr, hrone, hrepsilon, hHcore, hHout⟩ :=
    exists_supported_unit_cube_compression (ι := ι) epsilon hepsilon
  let Q := H.trans M
  have hHr (x : ι → ℝ) (hx : x ∈ closedBall (0 : ι → ℝ) 1) : ‖H x‖ ≤ r := by
    rw [hHcore x (mem_closedBall_zero_iff.mp hx), norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.mp hx)
  have hplace : MapsTo Q (closedBall (0 : ι → ℝ) 1) (A '' P) := by
    intro x hx
    have hmem : H x ∈ U := hball (mem_ball_zero_iff.mpr ((hHr x hx).trans_lt hrepsilon))
    change M (H x) ∈ A '' P
    exact image_mono interior_subset hmem
  obtain ⟨_, S, _, _, _, e, ⟨f, ⟨K, hK, hKC, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_unit_cube (ι := ι))
  let a : (ι → ℝ) →ᴬ[ℝ] (ι → ℝ) := r • ContinuousAffineMap.id ℝ (ι → ℝ)
  have ha : FinitePiecewiseAffineOn a (closedBall (0 : ι → ℝ) 1) := by
    rw [← hKC]
    exact (K.affineOnFaces_affine a).finitePiecewiseAffineOn hK
  have hmap : MapsTo a (closedBall (0 : ι → ℝ) 1) (closedBall (0 : ι → ℝ) 2) := by
    intro x hx
    apply mem_closedBall_zero_iff.mpr
    change ‖r • x‖ ≤ 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.mp hx)).trans
      (hrone.trans (by norm_num))
  have hQPL : FinitePiecewiseAffineOn Q (closedBall (0 : ι → ℝ) 1) :=
    (hMPL.comp ha hmap).congr (by
      intro x hx
      change M (r • x) = M (H x)
      rw [hHcore x (mem_closedBall_zero_iff.mp hx)])
  refine ⟨Q, hQPL, ?_, hplace⟩
  intro x hx
  change M (H x) = x
  rw [hHout x hx, hMout x hx]

end PoincareConjecture.M76
