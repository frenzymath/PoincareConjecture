import PoincareConjecture.Proofs.M76.Mathlib.ConvexCubeNormalization

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

theorem IsFinitePLBallPair.exists_cube_chart {s b : Set X}
    (hs : IsFinitePLBallPair E s b) {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : E ≃L[ℝ] (ι → ℝ)) :
    ∃ e : s ≃ₜ Metric.closedBall (0 : ι → ℝ) 1, e.IsFinitePL ∧
      ∀ x : s, (x : X) ∈ b ↔
        (e x : ι → ℝ) ∈ frontier (Metric.closedBall (0 : ι → ℝ) 1) := by
  obtain ⟨_, C, hC, hcv, hne, e, he, heb⟩ := hs
  have hcopy := he.symm
  obtain ⟨_, ⟨K, hK, hspace, _⟩, _⟩ := hcopy
  obtain ⟨H, hH, hHb⟩ := hC.exists_finitePL_cube_homeomorph hcv hne K hK hspace c
  exact ⟨e.trans H, he.trans hH, fun x => (heb x).trans (hHb (e x))⟩

theorem IsFinitePLBallPair.exists_homeomorph [Nontrivial E]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {s b : Set X} {t d : Set Y} (hs : IsFinitePLBallPair E s b)
    (ht : IsFinitePLBallPair E t d) :
    ∃ e : s ≃ₜ t, e.IsFinitePL ∧ ∀ x : s, (x : X) ∈ b ↔ (e x : Y) ∈ d := by
  let n := Module.finrank ℝ E
  have hn : 0 < n := Module.finrank_pos
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let c : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  obtain ⟨e, he, heb⟩ := hs.exists_cube_chart c
  obtain ⟨f, hf, hfd⟩ := ht.exists_cube_chart c
  refine ⟨e.trans f.symm, he.trans hf.symm, fun x => ?_⟩
  have h := hfd (f.symm (e x))
  rw [f.apply_symm_apply] at h
  exact (heb x).trans h.symm

end Set
