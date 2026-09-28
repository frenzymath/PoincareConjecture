import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.RadialTransition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.MatchingBalls

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace PoincareConjecture.SphereCharts

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem nonempty_diffeomorph_of_matching_balls
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    (b₀ b₁ : OpenPartialHomeomorph E3 M)
    {r : ℝ} (hr : 0 < r)
    (hs₀ : ball 0 (Real.exp r) ⊆ b₀.source)
    (hs₁ : ball 0 (Real.exp r) ⊆ b₁.source)
    (hb₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₀ b₀.source)
    (hb₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₁ b₁.source)
    (hbi₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₀.symm b₀.target)
    (hbi₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₁.symm b₁.target)
    (hcover : b₀ '' closedBall 0 1 ∪ b₁ '' closedBall 0 1 = univ)
    (hintersection : b₀ '' closedBall 0 1 ∩ b₁ '' closedBall 0 1 = b₀ '' sphere 0 1)
    (hmatch : ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r →
      b₀ (Real.exp t • (q : E3)) = b₁ (Real.exp (-t) • (q : E3))) :
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M UnitThreeSphere ∞) := by
  let e₀ := (b₀.restrOpen (ball 0 (Real.exp r)) isOpen_ball).symm
  let e₁ := (b₁.restrOpen (ball 0 (Real.exp r)) isOpen_ball).symm
  have htarget (b : OpenPartialHomeomorph E3 M) (hs : ball 0 (Real.exp r) ⊆ b.source) :
      (b.restrOpen (ball 0 (Real.exp r)) isOpen_ball).source = ball 0 (Real.exp r) :=
    inter_eq_right.mpr hs
  have hsource (b : OpenPartialHomeomorph E3 M) (hs : ball 0 (Real.exp r) ⊆ b.source) :
      (b.restrOpen (ball 0 (Real.exp r)) isOpen_ball).target = b '' ball 0 (Real.exp r) := by
    rw [← OpenPartialHomeomorph.image_source_eq_target, htarget b hs]
    rfl
  have hsmall : closedBall (0 : E3) 1 ⊆ ball 0 (Real.exp r) :=
    closedBall_subset_ball (by simpa using Real.exp_lt_exp.mpr hr)
  have hcover' : e₀.source ∪ e₁.source = univ := by
    change (b₀.restrOpen _ isOpen_ball).target ∪ (b₁.restrOpen _ isOpen_ball).target = univ
    rw [hsource b₀ hs₀, hsource b₁ hs₁]
    apply eq_univ_of_univ_subset
    rw [← hcover]
    exact union_subset_union (image_mono hsmall) (image_mono hsmall)
  let v : UnitThreeSphere := Classical.choice
    (NormedSpace.sphere_nonempty.mpr (zero_le_one : (0 : ℝ) ≤ 1)).coe_sort
  let c₀ := radialSphereBallChart v r
  let c₁ := oppositeRadialSphereBallChart v r
  have he₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₀ e₀.source := hbi₀.mono inter_subset_left
  have he₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₁ e₁.source := hbi₁.mono inter_subset_left
  have hei₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₀.symm e₀.target := hb₀.mono inter_subset_left
  have hei₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₁.symm e₁.target := hb₁.mono inter_subset_left
  have htrans : OpenPartialHomeomorph.EqOnSource (e₀.symm.trans e₁) (c₀.symm.trans c₁) := by
    have hedomain := Poincare.matching_ball_transition_source b₀ b₁ hr hs₀ hs₁
      hintersection hmatch
    refine ⟨hedomain.trans (radialSphereBallChart_transition_source v r).symm, ?_⟩
    intro x hx
    have hx' : Real.exp (-r) < ‖x‖ ∧ ‖x‖ < Real.exp r := hedomain.subset hx
    change b₁.symm (b₀ x) = oppositeRadialSphereBallChart v r ((radialSphereBallChart v r).symm x)
    rw [Poincare.inverse_of_matching_balls b₀ b₁ hs₁ hmatch
      (mem_ball_zero_iff.mpr hx'.2) hx'.1,
      radialSphereBallChart_transition v r x
        (norm_pos_iff.mp ((Real.exp_pos (-r)).trans hx'.1))]
  obtain ⟨d, _⟩ := OpenPartialHomeomorph.exists_diffeomorph_of_chart_transition
    e₀ e₁ c₀ c₁ hcover' (radialSphereBallChart_source_union v r hr)
    ((htarget b₀ hs₀).trans (radialSphereBallChart_target v r).symm)
    ((htarget b₁ hs₁).trans (oppositeRadialSphereBallChart_target v r).symm)
    he₀ he₁ hei₀ hei₁
    (radialSphereBallChart_contMDiff v r).1 (oppositeRadialSphereBallChart_contMDiff v r).1
    (radialSphereBallChart_contMDiff v r).2 (oppositeRadialSphereBallChart_contMDiff v r).2 htrans
  exact ⟨d⟩

theorem nonempty_diffeomorph_of_matching_balls_in_open
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
    (U : TopologicalSpace.Opens M) (hU : Nonempty U)
    (b₀ b₁ : OpenPartialHomeomorph E3 M)
    {r : ℝ} (hr : 0 < r)
    (hs₀ : ball 0 (Real.exp r) ⊆ b₀.source)
    (hs₁ : ball 0 (Real.exp r) ⊆ b₁.source)
    (ht₀ : b₀.target ⊆ U) (ht₁ : b₁.target ⊆ U)
    (hb₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₀ b₀.source)
    (hb₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₁ b₁.source)
    (hbi₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₀.symm b₀.target)
    (hbi₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b₁.symm b₁.target)
    (hcover : b₀ '' closedBall 0 1 ∪ b₁ '' closedBall 0 1 = (U : Set M))
    (hintersection : b₀ '' closedBall 0 1 ∩ b₁ '' closedBall 0 1 = b₀ '' sphere 0 1)
    (hmatch : ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r →
      b₀ (Real.exp t • (q : E3)) = b₁ (Real.exp (-t) • (q : E3))) :
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) U UnitThreeSphere ∞) := by
  let a (b : OpenPartialHomeomorph E3 M) := (b.symm.subtypeRestr hU).symm
  have has (b : OpenPartialHomeomorph E3 M) (ht : b.target ⊆ U) :
      (a b).source = b.source := by
    change b.source ∩ b ⁻¹' (U.openPartialHomeomorphSubtypeCoe hU).target = b.source
    rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
    exact inter_eq_left.mpr (fun x hx => ht (b.map_source hx))
  have hav (b : OpenPartialHomeomorph E3 M) (ht : b.target ⊆ U)
      (x : E3) (hx : x ∈ b.source) : (a b x : M) = b x :=
    b.symm.subtypeRestr_symm_apply hU ((has b ht).symm.subset hx)
  have ha (b : OpenPartialHomeomorph E3 M) (ht : b.target ⊆ U)
      (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source) :
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (a b) (a b).source := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U (a b) (a b).source x).mp
    apply ((hb x (has b ht ▸ hx)).mono (has b ht ▸ subset_rfl)).congr
    · intro y hy
      exact hav b ht y (has b ht ▸ hy)
    · exact hav b ht x (has b ht ▸ hx)
  have hai (b : OpenPartialHomeomorph E3 M)
      (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target) :
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (a b).symm (a b).target := by
    have h := hbi.comp (contMDiff_subtype_val (U := U)).contMDiffOn (fun _ hx => hx)
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (b.symm.subtypeRestr hU)
      (b.symm.subtypeRestr hU).source
    rw [OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.subtypeRestr_coe]
    exact h
  have himage (b : OpenPartialHomeomorph E3 M) (ht : b.target ⊆ U)
      (S : Set E3) (hS : S ⊆ b.source) :
      (Subtype.val : U → M) '' (a b '' S) = b '' S := by
    rw [image_image]
    exact image_congr (fun x hx => hav b ht x (hS hx))
  have hsmall : closedBall (0 : E3) 1 ⊆ ball 0 (Real.exp r) :=
    closedBall_subset_ball (by simpa using Real.exp_lt_exp.mpr hr)
  have hclosed₀ := hsmall.trans hs₀
  have hclosed₁ := hsmall.trans hs₁
  apply nonempty_diffeomorph_of_matching_balls (a b₀) (a b₁) hr
    (has b₀ ht₀ ▸ hs₀) (has b₁ ht₁ ▸ hs₁)
    (ha b₀ ht₀ hb₀) (ha b₁ ht₁ hb₁) (hai b₀ hbi₀) (hai b₁ hbi₁)
  · apply image_injective.mpr Subtype.val_injective
    rw [image_union, himage b₀ ht₀ _ hclosed₀, himage b₁ ht₁ _ hclosed₁, hcover]
    simp
  · apply image_injective.mpr Subtype.val_injective
    rw [image_inter Subtype.val_injective, himage b₀ ht₀ _ hclosed₀,
      himage b₁ ht₁ _ hclosed₁, himage b₀ ht₀ _ (sphere_subset_closedBall.trans hclosed₀),
      hintersection]
  · intro q t ht
    have hx : Real.exp t • (q : E3) ∈ ball (0 : E3) (Real.exp r) := by
      simpa [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, Real.abs_exp] using
        Real.exp_lt_exp.mpr (abs_lt.mp ht).2
    have hy : Real.exp (-t) • (q : E3) ∈ ball (0 : E3) (Real.exp r) := by
      simpa [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, Real.abs_exp] using
        Real.exp_lt_exp.mpr (show -t < r by linarith [(abs_lt.mp ht).1])
    apply Subtype.ext
    rw [hav b₀ ht₀ _ (hs₀ hx), hav b₁ ht₁ _ (hs₁ hy), hmatch q t ht]

end PoincareConjecture.SphereCharts
