import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.PointAdjustment









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => sphere (0 : E3) 1



theorem exists_ball_preserving_centering {a : E3} (ha : ‖a‖ < 1) :
    ∃ (η : ℝ) (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < η ∧ F 0 = a ∧ F '' closedBall 0 1 = closedBall 0 1 ∧
      ∀ (q : S2) (t : ℝ), |t| < η → F (Real.exp t • (q : E3)) = Real.exp t • (q : E3) := by
  obtain ⟨r, F, hr, hr1, hF0, hfix⟩ := exists_diffeomorph_move_zero_in_unitBall ha
  have hball : F '' closedBall 0 1 = closedBall 0 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_contra hy
      have hnorm : 1 < ‖F x‖ := by simpa using hy
      have heq : F x = x := F.injective (hfix (F x) (hr1.le.trans hnorm.le))
      exact hy (heq.symm ▸ hx)
    · intro hy
      refine ⟨F.symm y, ?_, F.apply_symm_apply y⟩
      by_contra hx
      have hnorm : 1 < ‖F.symm y‖ := by simpa using hx
      have heq : y = F.symm y := (F.apply_symm_apply y).symm.trans
        (hfix (F.symm y) (hr1.le.trans hnorm.le))
      exact hx (heq ▸ hy)
  let η := -Real.log r / 2
  have hlog : Real.log r < 0 := Real.log_neg hr hr1
  have hη : 0 < η := by dsimp [η]; linarith
  have hrη : r < Real.exp (-η) := by
    rw [← Real.exp_log hr]
    apply Real.exp_lt_exp.mpr
    dsimp [η]
    linarith
  refine ⟨η, F, hη, hF0, hball, ?_⟩
  intro q t ht
  apply hfix
  have hrt : r < Real.exp t := hrη.trans (Real.exp_lt_exp.mpr (abs_lt.mp ht).1)
  simpa [norm_smul, Real.norm_eq_abs, Real.abs_exp] using hrt.le



theorem exists_centered_ball_neighborhood
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    (b : OpenPartialHomeomorph E3 M)
    (hs : closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    {p : M} (hp : p ∈ b '' ball 0 1) :
    ∃ (η : ℝ) (c : OpenPartialHomeomorph E3 M),
      0 < η ∧ closedBall 0 1 ⊆ c.source ∧ c.target = b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ c c.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target ∧
      c '' closedBall 0 1 = b '' closedBall 0 1 ∧ c 0 = p ∧
      ∀ (q : S2) (t : ℝ), |t| < η →
        (Real.exp t • (q : E3) ∈ c.source ↔ Real.exp t • (q : E3) ∈ b.source) ∧
        c (Real.exp t • (q : E3)) = b (Real.exp t • (q : E3)) := by
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨η, F, hη, hF0, hFball, hfix⟩ := exists_ball_preserving_centering (mem_ball_zero_iff.mp ha)
  let c := F.toHomeomorph.toOpenPartialHomeomorph.trans b
  refine ⟨η, c, hη, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨mem_univ _, hs (hFball ▸ mem_image_of_mem F hx)⟩
  · simp [c]
  · exact hb.comp F.contMDiff.contMDiffOn inter_subset_right
  · exact F.symm.contMDiff.comp_contMDiffOn (hbi.mono inter_subset_left)
  · change (b ∘ F) '' closedBall 0 1 = b '' closedBall 0 1
    calc
      (b ∘ F) '' closedBall 0 1 = b '' (F '' closedBall 0 1) :=
        (image_image (⇑b) (⇑F) _).symm
      _ = b '' closedBall 0 1 := by rw [hFball]
  · change b (F 0) = b a
    rw [hF0]
  · intro q t ht
    constructor
    · change (Real.exp t • (q : E3) ∈ univ ∧ F (Real.exp t • (q : E3)) ∈ b.source) ↔ _
      simp only [mem_univ, true_and, hfix q t ht]
    · change b (F (Real.exp t • (q : E3))) = _
      rw [hfix q t ht]

end Poincare
