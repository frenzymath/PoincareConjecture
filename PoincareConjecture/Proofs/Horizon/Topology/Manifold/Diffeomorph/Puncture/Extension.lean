import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCylinder
import Mathlib.Analysis.Normed.Module.Connected










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "S2" => Metric.sphere (0 : E3) 1



theorem exists_euclidean_extension_of_punctured_identity
    (H : Diffeomorph (𝓡 3) (𝓡 3) puncturedThreeSpace puncturedThreeSpace ∞)
    {r : ℝ} (hr : 0 < r)
    (hfix : ∀ x : puncturedThreeSpace, ‖(x : E3)‖ < r → H x = x) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ x : puncturedThreeSpace, F x = (H x : E3)) ∧
      ∀ x : E3, ‖x‖ < r → F x = x := by
  classical
  let extend (G : puncturedThreeSpace → puncturedThreeSpace) (x : E3) : E3 :=
    if hx : x = 0 then 0 else G ⟨x, hx⟩
  have extend_coe (G : puncturedThreeSpace → puncturedThreeSpace)
      (x : puncturedThreeSpace) : extend G x = (G x : E3) := by
    dsimp [extend]
    rw [dif_neg (show (x : E3) ≠ 0 from x.property)]
  have extend_zero (G : puncturedThreeSpace → puncturedThreeSpace) : extend G 0 = 0 := by
    simp [extend]
  have extend_fix (G : puncturedThreeSpace → puncturedThreeSpace)
      (hG : ∀ x : puncturedThreeSpace, ‖(x : E3)‖ < r → G x = x)
      (x : E3) (hx : ‖x‖ < r) : extend G x = x := by
    by_cases hzero : x = 0
    · rw [hzero, extend_zero]
    · exact (extend_coe G ⟨x, hzero⟩).trans (congrArg Subtype.val (hG ⟨x, hzero⟩ hx))
  have extend_smooth (G : Diffeomorph (𝓡 3) (𝓡 3)
      puncturedThreeSpace puncturedThreeSpace ∞)
      (hG : ∀ x : puncturedThreeSpace, ‖(x : E3)‖ < r → G x = x) :
      ContMDiff (𝓡 3) (𝓡 3) ∞ (extend G) := by
    intro x
    by_cases hx : x = 0
    · subst x
      apply contMDiffAt_id.congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds (0 : E3) hr] with y hy
      exact extend_fix G hG y (by simpa using hy)
    · apply (contMDiffAt_subtype_iff (U := puncturedThreeSpace) (x := ⟨x, hx⟩)).mp
      have heq : (fun y : puncturedThreeSpace => extend G y) =
          (fun y : puncturedThreeSpace => (G y : E3)) := funext (extend_coe G)
      rw [heq]
      exact (contMDiff_subtype_val.comp G.contMDiff).contMDiffAt
  have hfixi (x : puncturedThreeSpace) (hx : ‖(x : E3)‖ < r) : H.symm x = x := by
    apply H.injective
    change H (H.symm x) = H x
    rw [H.apply_symm_apply, hfix x hx]
  have hinv (G : Diffeomorph (𝓡 3) (𝓡 3)
      puncturedThreeSpace puncturedThreeSpace ∞) (x : E3) :
      extend G.symm (extend G x) = x := by
    by_cases hx : x = 0
    · rw [hx, extend_zero, extend_zero]
    · rw [extend_coe G ⟨x, hx⟩, extend_coe G.symm (G ⟨x, hx⟩), G.symm_apply_apply]
  let F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := {
    toFun := extend H
    invFun := extend H.symm
    left_inv := hinv H
    right_inv := hinv H.symm
    contMDiff_toFun := extend_smooth H hfix
    contMDiff_invFun := extend_smooth H.symm hfixi }
  exact ⟨F, extend_coe H, extend_fix H hfix⟩



theorem exists_euclidean_extension_of_cylinder_negative_tail
    (K : Diffeomorph CylModel CylModel (S2 × ℝ) (S2 × ℝ) ∞)
    (R : ℝ) (hfix : ∀ p : S2 × ℝ, p.2 < -R → K p = p) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ p : S2 × ℝ, F (Real.exp p.2 • (p.1 : E3)) =
        Real.exp (K p).2 • ((K p).1 : E3)) ∧
      ∀ x : E3, ‖x‖ < Real.exp (-R) → F x = x := by
  let J := sphereCylinderDiffeomorphPunctured
  let H := (J.symm.trans K).trans J
  have hH (x : puncturedThreeSpace) (hx : ‖(x : E3)‖ < Real.exp (-R)) : H x = x := by
    have hp : (J.symm x).2 < -R := by
      have hnorm : ‖(x : E3)‖ = Real.exp (J.symm x).2 := by
        calc
          ‖(x : E3)‖ = ‖(J (J.symm x) : E3)‖ := by rw [J.apply_symm_apply]
          _ = Real.exp (J.symm x).2 := by
            rw [sphereCylinderDiffeomorphPunctured_apply, norm_smul]
            simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [hnorm] at hx
      exact Real.exp_lt_exp.mp hx
    change J (K (J.symm x)) = x
    rw [hfix _ hp, J.apply_symm_apply]
  obtain ⟨F, hF, hzero⟩ := exists_euclidean_extension_of_punctured_identity
    H (Real.exp_pos (-R)) hH
  refine ⟨F, ?_, hzero⟩
  intro p
  have hp := hF (J p)
  change F (Real.exp p.2 • (p.1 : E3)) = (J (K (J.symm (J p))) : E3) at hp
  rw [J.symm_apply_apply] at hp
  exact hp



theorem image_closedBall_of_fixing_zero_and_sphere
    (F : E3 ≃ₜ E3) (hzero : F 0 = 0)
    (hsphere : ∀ q : S2, F q = (q : E3)) :
    F '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
  have hball (G : E3 ≃ₜ E3) (hz : G 0 = 0)
      (hS : ∀ q : S2, G q = (q : E3)) :
      G '' Metric.ball 0 1 ⊆ Metric.ball 0 1 := by
    have hc : IsPreconnected (G '' Metric.ball 0 1) :=
      Metric.isPreconnected_ball.image G G.continuous.continuousOn
    apply hc.subset_left_of_subset_union Metric.isOpen_ball
      Metric.isClosed_closedBall.isOpen_compl
      (disjoint_left.mpr fun _ hx hy => hy (Metric.ball_subset_closedBall hx))
    · rintro _ ⟨x, hx, rfl⟩
      have hne : ‖G x‖ ≠ 1 := by
        intro heq
        have hmem : G x ∈ Metric.sphere (0 : E3) 1 := by simpa using heq
        have hfix := hS ⟨G x, hmem⟩
        have hxx : G x = x := G.injective hfix
        have hx' : ‖x‖ < 1 := by simpa using hx
        rw [hxx] at heq
        exact hx'.ne heq
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (by simpa using hlt)
      · exact Or.inr (by simpa using hgt)
    · exact ⟨0, ⟨0, Metric.mem_ball_self (by norm_num), hz⟩,
        Metric.mem_ball_self (by norm_num)⟩
  have hclosed (G : E3 ≃ₜ E3) (hz : G 0 = 0)
      (hS : ∀ q : S2, G q = (q : E3)) :
      G '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 1 := by
    rw [← closure_ball (0 : E3) one_ne_zero, G.image_closure]
    exact closure_mono (hball G hz hS)
  apply Subset.antisymm (hclosed F hzero hsphere)
  intro x hx
  have hzi : F.symm 0 = 0 := F.injective (by rw [F.apply_symm_apply, hzero])
  have hsi (q : S2) : F.symm q = (q : E3) :=
    F.injective (by rw [F.apply_symm_apply, hsphere q])
  exact ⟨F.symm x, hclosed F.symm hzi hsi (mem_image_of_mem F.symm hx),
    F.apply_symm_apply x⟩



theorem exists_ball_preserving_extension_of_cylinder_negative_tail
    (K : Diffeomorph CylModel CylModel (S2 × ℝ) (S2 × ℝ) ∞)
    (R : ℝ) (hfix : ∀ p : S2 × ℝ, p.2 < -R → K p = p)
    (hzero : ∀ q : S2, K (q, 0) = (q, 0)) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' Metric.closedBall 0 1 = Metric.closedBall 0 1 ∧
      (∀ p : S2 × ℝ, F (Real.exp p.2 • (p.1 : E3)) =
        Real.exp (K p).2 • ((K p).1 : E3)) ∧
      ∀ x : E3, ‖x‖ < Real.exp (-R) → F x = x := by
  obtain ⟨F, hF, hsmall⟩ := exists_euclidean_extension_of_cylinder_negative_tail K R hfix
  have hF0 : F 0 = 0 := hsmall 0 (by simpa using Real.exp_pos (-R))
  have hFS (q : S2) : F q = (q : E3) := by
    simpa [hzero q] using hF (q, 0)
  exact ⟨F, image_closedBall_of_fixing_zero_and_sphere F.toHomeomorph hF0 hFS, hF, hsmall⟩

end Poincare
