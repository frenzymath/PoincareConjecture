import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Nesting



set_option autoImplicit false

open Set Metric

namespace Poincare.Manifold.Schoenflies.Reverse



theorem norm_le_on_filled_ball_of_boundary_bound
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [ProperSpace E]
    [NormedAddCommGroup V] [NormedSpace Real V]
    (B : E ≃ₜ E) (p : E → V) (hp : Continuous p) (hpo : IsOpenMap p)
    {c : Real} (hc : 0 ≤ c)
    (hboundary : ∀ y ∈ B '' sphere (0 : E) 1, ‖p y‖ ≤ c) :
    ∀ y ∈ B '' closedBall (0 : E) 1, ‖p y‖ ≤ c := by
  have hK : IsCompact (B '' closedBall (0 : E) 1) :=
    (isCompact_closedBall 0 1).image B.continuous
  have hne : (B '' closedBall (0 : E) 1).Nonempty :=
    ⟨B 0, mem_image_of_mem B (by simp)⟩
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne hp.norm.continuousOn
  suffices hzc : ‖p z‖ ≤ c by
    intro y hy
    exact (hmax hy).trans hzc
  by_contra hn
  have hpos : 0 < ‖p z‖ := hc.trans_lt (lt_of_not_ge hn)
  have hzopen : z ∈ B '' ball (0 : E) 1 := by
    obtain ⟨x, hx, rfl⟩ := hz
    refine mem_image_of_mem B (mem_ball_zero_iff.mpr ?_)
    have hle := mem_closedBall_zero_iff.mp hx
    by_contra hnot
    have heq : ‖x‖ = 1 := le_antisymm hle (le_of_not_gt hnot)
    exact hn (hboundary _ (mem_image_of_mem B (mem_sphere_zero_iff_norm.mpr heq)))
  have hopen : IsOpen (p '' (B '' ball (0 : E) 1)) :=
    hpo _ (B.isOpenMap _ isOpen_ball)
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen _ (mem_image_of_mem p hzopen)
  let a : Real := 1 + ε / (2 * ‖p z‖)
  have ha : 0 < a := by dsimp [a]; positivity
  have hεeq : ε / (2 * ‖p z‖) * ‖p z‖ = ε / 2 := by field_simp
  have hnear : a • p z ∈ ball (p z) ε := by
    rw [mem_ball, dist_eq_norm, show a • p z - p z = (a - 1) • p z by
      rw [sub_smul, one_smul]]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ a - 1 by
      dsimp [a]
      linarith [div_pos hε (mul_pos (by norm_num : (0 : Real) < 2) hpos)])]
    dsimp [a]
    rw [add_sub_cancel_left, hεeq]
    linarith
  obtain ⟨w, hw, heq⟩ := hεsub hnear
  have hle := hmax ((image_mono ball_subset_closedBall) hw)
  change ‖p w‖ ≤ ‖p z‖ at hle
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hle
  dsimp [a] at hle
  rw [add_mul, one_mul, hεeq] at hle
  linarith

end Poincare.Manifold.Schoenflies.Reverse
