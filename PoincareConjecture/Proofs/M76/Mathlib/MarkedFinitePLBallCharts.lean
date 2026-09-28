import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.ConvexSpherePoleNormalization

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

theorem IsFinitePLBallPair.exists_cube_chart_boundary_point {s b : Set X}
    (hs : IsFinitePLBallPair E s b) {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : E ≃L[ℝ] (ι → ℝ)) (p : b) :
    ∃ e : s ≃ₜ Metric.closedBall (0 : ι → ℝ) 1, e.IsFinitePL ∧
      (∀ x : s, (x : X) ∈ b ↔
        (e x : ι → ℝ) ∈ frontier (Metric.closedBall (0 : ι → ℝ) 1)) ∧
      (e ⟨p, hs.1 p.property⟩ : ι → ℝ) = fun _ => 1 := by
  obtain ⟨e, he, heb⟩ := hs.exists_cube_chart c
  let T := Metric.closedBall (0 : ι → ℝ) 1
  have hT : IsCompact T := isCompact_closedBall _ _
  have hTcv : Convex ℝ T := convex_closedBall _ _
  have hTne : (interior T).Nonempty :=
    ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self zero_lt_one)⟩
  have htri := he.symm
  obtain ⟨_, ⟨K, hK, hspace, _⟩, _⟩ := htri
  let q : frontier T := ⟨e ⟨p, hs.1 p.property⟩, (heb _).mp p.property⟩
  obtain ⟨eb, hebPL, hebq⟩ :=
    (K.frontierSubcomplex T).exists_finitePL_convex_frontier_cube_pole
      (K.frontierSubcomplex_finite T hK) hT hTcv hTne
      (K.frontierSubcomplex_space hT.isClosed hTcv hTne hspace)
      (ContinuousLinearEquiv.refl ℝ (ι → ℝ)) q
  obtain ⟨H, hH, hHb, hHmem⟩ := hebPL.exists_convex_extension hT hT hTcv hTcv hTne hTne
  refine ⟨e.trans H, he.trans hH, fun x => (heb x).trans (hHmem (e x)), ?_⟩
  have hq : e ⟨p, hs.1 p.property⟩ = ⟨q, hT.isClosed.frontier_subset q.property⟩ :=
    Subtype.ext rfl
  change (H (e ⟨p, hs.1 p.property⟩) : ι → ℝ) = fun _ => 1
  rw [hq, hHb]
  exact hebq

theorem IsFinitePLBallPair.exists_homeomorph_boundary_point [Nontrivial E]
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {s b : Set X} {t d : Set Y} (hs : IsFinitePLBallPair E s b)
    (ht : IsFinitePLBallPair E t d) (p : b) (q : d) :
    ∃ e : s ≃ₜ t, e.IsFinitePL ∧
      (∀ x : s, (x : X) ∈ b ↔ (e x : Y) ∈ d) ∧
      e ⟨p, hs.1 p.property⟩ = ⟨q, ht.1 q.property⟩ := by
  let n := Module.finrank ℝ E
  have hn : 0 < n := Module.finrank_pos
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let c : E ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  obtain ⟨e, he, heb, hep⟩ := hs.exists_cube_chart_boundary_point c p
  obtain ⟨f, hf, hfd, hfq⟩ := ht.exists_cube_chart_boundary_point c q
  refine ⟨e.trans f.symm, he.trans hf.symm, fun x => ?_, ?_⟩
  · have h := hfd (f.symm (e x))
    rw [f.apply_symm_apply] at h
    exact (heb x).trans h.symm
  · apply f.injective
    change f (f.symm (e ⟨p, hs.1 p.property⟩)) = f ⟨q, ht.1 q.property⟩
    rw [f.apply_symm_apply]
    exact Subtype.ext (hep.trans hfq.symm)

end Set
