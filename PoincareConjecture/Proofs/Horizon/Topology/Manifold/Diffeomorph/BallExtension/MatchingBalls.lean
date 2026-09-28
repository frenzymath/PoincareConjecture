import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCylinder

set_option autoImplicit false

open Set Metric

namespace Poincare

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1

private theorem radial_representation_above_one {x : E3} (hx : 1 < ‖x‖)
    {r : ℝ} (hr : ‖x‖ < Real.exp r) :
    ∃ q : S2, ∃ t : ℝ, 0 < t ∧ t < r ∧ x = Real.exp t • (q : E3) := by
  have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx
  let J := sphereCylinderDiffeomorphPunctured
  let p := J.symm ⟨x, hx0⟩
  have hp : Real.exp p.2 • (p.1 : E3) = x :=
    congrArg Subtype.val (J.apply_symm_apply ⟨x, hx0⟩)
  have hnorm : Real.exp p.2 = ‖x‖ := by
    rw [← hp, norm_smul]
    simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine ⟨p.1, p.2, ?_, Real.exp_lt_exp.mp (hnorm.symm ▸ hr), hp.symm⟩
  apply Real.exp_lt_exp.mp
  simpa only [Real.exp_zero, hnorm] using hx

theorem eq_iff_radial_of_matching_balls
    {M : Type*} [TopologicalSpace M]
    (b₀ b₁ : OpenPartialHomeomorph E3 M)
    {r : ℝ} (hr : 0 < r)
    (hs₀ : ball 0 (Real.exp r) ⊆ b₀.source)
    (hs₁ : ball 0 (Real.exp r) ⊆ b₁.source)
    (hintersection : b₀ '' closedBall 0 1 ∩ b₁ '' closedBall 0 1 = b₀ '' sphere 0 1)
    (hmatch : ∀ (q : S2) (t : ℝ), |t| < r →
      b₀ (Real.exp t • (q : E3)) = b₁ (Real.exp (-t) • (q : E3)))
    {x y : E3} (hx : x ∈ ball 0 (Real.exp r)) (hy : y ∈ ball 0 (Real.exp r)) :
    b₀ x = b₁ y ↔ ∃ q : S2, ∃ t : ℝ,
      |t| < r ∧ x = Real.exp t • (q : E3) ∧ y = Real.exp (-t) • (q : E3) := by
  have hrad (q : S2) {t : ℝ} (ht : t < r) :
      Real.exp t • (q : E3) ∈ ball (0 : E3) (Real.exp r) := by
    simpa [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, Real.abs_exp] using
      Real.exp_lt_exp.mpr ht
  have hsmall : closedBall (0 : E3) 1 ⊆ ball 0 (Real.exp r) :=
    closedBall_subset_ball (by simpa using Real.exp_lt_exp.mpr hr)
  constructor
  · intro heq
    by_cases hxlarge : 1 < ‖x‖
    · obtain ⟨q, t, ht, htr, hxt⟩ :=
        radial_representation_above_one hxlarge (mem_ball_zero_iff.mp hx)
      have habs : |t| < r := by simpa only [abs_of_pos ht] using htr
      refine ⟨q, t, habs, hxt, ?_⟩
      apply b₁.injOn (hs₁ hy) (hs₁ (hrad q (by linarith)))
      exact heq.symm.trans (hxt ▸ hmatch q t habs)
    · by_cases hylarge : 1 < ‖y‖
      · obtain ⟨q, t, ht, htr, hyt⟩ :=
          radial_representation_above_one hylarge (mem_ball_zero_iff.mp hy)
        have habs : |-t| < r := by simpa only [abs_neg, abs_of_pos ht] using htr
        refine ⟨q, -t, habs, ?_, by simpa only [neg_neg] using hyt⟩
        apply b₀.injOn (hs₀ hx) (hs₀ (hrad q (by linarith)))
        have hh := hmatch q (-t) habs
        rw [neg_neg, ← hyt] at hh
        exact heq.trans hh.symm
      · have hxclosed : x ∈ closedBall (0 : E3) 1 := by simpa using le_of_not_gt hxlarge
        have hyclosed : y ∈ closedBall (0 : E3) 1 := by simpa using le_of_not_gt hylarge
        have hi : b₀ x ∈ b₀ '' sphere 0 1 := hintersection.subset
          ⟨mem_image_of_mem b₀ hxclosed, heq ▸ mem_image_of_mem b₁ hyclosed⟩
        obtain ⟨z, hz, hzx⟩ := hi
        have hzx' : z = x := b₀.injOn
          (hs₀ (hsmall (sphere_subset_closedBall hz))) (hs₀ hx) hzx
        have hxsphere : x ∈ sphere (0 : E3) 1 := hzx' ▸ hz
        let q : S2 := ⟨x, hxsphere⟩
        have hxy : y = x := by
          apply b₁.injOn (hs₁ hy) (hs₁ hx)
          have hh := hmatch q 0 (by simpa using hr)
          simp only [Real.exp_zero, neg_zero, one_smul] at hh
          exact heq.symm.trans hh
        exact ⟨q, 0, by simpa using hr, by simp [q], by simpa [q] using hxy⟩
  · rintro ⟨q, t, ht, rfl, rfl⟩
    exact hmatch q t ht

theorem mem_matching_ball_overlap_iff
    {M : Type*} [TopologicalSpace M]
    (b₀ b₁ : OpenPartialHomeomorph E3 M)
    {r : ℝ} (hr : 0 < r)
    (hs₀ : ball 0 (Real.exp r) ⊆ b₀.source)
    (hs₁ : ball 0 (Real.exp r) ⊆ b₁.source)
    (hintersection : b₀ '' closedBall 0 1 ∩ b₁ '' closedBall 0 1 = b₀ '' sphere 0 1)
    (hmatch : ∀ (q : S2) (t : ℝ), |t| < r →
      b₀ (Real.exp t • (q : E3)) = b₁ (Real.exp (-t) • (q : E3)))
    {x : E3} (hx : x ∈ ball 0 (Real.exp r)) :
    b₀ x ∈ b₁ '' ball 0 (Real.exp r) ↔ Real.exp (-r) < ‖x‖ := by
  constructor
  · rintro ⟨y, hy, heq⟩
    obtain ⟨q, t, ht, rfl, _⟩ :=
      (eq_iff_radial_of_matching_balls b₀ b₁ hr hs₀ hs₁ hintersection hmatch hx hy).mp heq.symm
    simpa [norm_smul, Real.norm_eq_abs, Real.abs_exp] using
      Real.exp_lt_exp.mpr (abs_lt.mp ht).1
  · intro hnorm
    have hx0 : x ≠ 0 := norm_pos_iff.mp ((Real.exp_pos (-r)).trans hnorm)
    let J := sphereCylinderDiffeomorphPunctured
    let p := J.symm ⟨x, hx0⟩
    have hp : Real.exp p.2 • (p.1 : E3) = x :=
      congrArg Subtype.val (J.apply_symm_apply ⟨x, hx0⟩)
    have hn : Real.exp p.2 = ‖x‖ := by
      rw [← hp, norm_smul]
      simp [Real.norm_eq_abs, Real.abs_exp]
    have ht : |p.2| < r := abs_lt.mpr
      ⟨Real.exp_lt_exp.mp (hn.symm ▸ hnorm),
        Real.exp_lt_exp.mp (hn.symm ▸ mem_ball_zero_iff.mp hx)⟩
    refine ⟨Real.exp (-p.2) • (p.1 : E3), ?_, ?_⟩
    · simpa [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, Real.abs_exp] using
        Real.exp_lt_exp.mpr (show -p.2 < r by linarith [(abs_lt.mp ht).1])
    · exact (hmatch p.1 p.2 ht).symm.trans (congrArg b₀ hp)

theorem inverse_of_matching_balls
    {M : Type*} [TopologicalSpace M]
    (b₀ b₁ : OpenPartialHomeomorph E3 M)
    {r : ℝ}
    (hs₁ : ball 0 (Real.exp r) ⊆ b₁.source)
    (hmatch : ∀ (q : S2) (t : ℝ), |t| < r →
      b₀ (Real.exp t • (q : E3)) = b₁ (Real.exp (-t) • (q : E3)))
    {x : E3} (hx : x ∈ ball 0 (Real.exp r)) (hxlow : Real.exp (-r) < ‖x‖) :
    b₁.symm (b₀ x) = (‖x‖ ^ 2)⁻¹ • x := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((Real.exp_pos (-r)).trans hxlow)
  let J := sphereCylinderDiffeomorphPunctured
  let p := J.symm ⟨x, hx0⟩
  have hp : Real.exp p.2 • (p.1 : E3) = x :=
    congrArg Subtype.val (J.apply_symm_apply ⟨x, hx0⟩)
  have hn : Real.exp p.2 = ‖x‖ := by
    rw [← hp, norm_smul]
    simp [Real.norm_eq_abs, Real.abs_exp]
  have ht : |p.2| < r := abs_lt.mpr
    ⟨Real.exp_lt_exp.mp (hn.symm ▸ hxlow),
      Real.exp_lt_exp.mp (hn.symm ▸ mem_ball_zero_iff.mp hx)⟩
  have hi : Real.exp (-p.2) • (p.1 : E3) ∈ b₁.source := by
    apply hs₁
    simpa [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, Real.abs_exp] using
      Real.exp_lt_exp.mpr (show -p.2 < r by linarith [(abs_lt.mp ht).1])
  calc
    b₁.symm (b₀ x) = Real.exp (-p.2) • (p.1 : E3) := by
      rw [← hp, hmatch p.1 p.2 ht, b₁.left_inv hi]
    _ = (‖x‖ ^ 2)⁻¹ • x := by
      rw [← hn, ← hp, smul_smul, Real.exp_neg]
      congr 1
      field_simp

theorem matching_ball_transition_source
    {M : Type*} [TopologicalSpace M]
    (b₀ b₁ : OpenPartialHomeomorph E3 M)
    {r : ℝ} (hr : 0 < r)
    (hs₀ : ball 0 (Real.exp r) ⊆ b₀.source)
    (hs₁ : ball 0 (Real.exp r) ⊆ b₁.source)
    (hintersection : b₀ '' closedBall 0 1 ∩ b₁ '' closedBall 0 1 = b₀ '' sphere 0 1)
    (hmatch : ∀ (q : S2) (t : ℝ), |t| < r →
      b₀ (Real.exp t • (q : E3)) = b₁ (Real.exp (-t) • (q : E3))) :
    ((b₀.restrOpen (ball 0 (Real.exp r)) isOpen_ball).trans
      (b₁.restrOpen (ball 0 (Real.exp r)) isOpen_ball).symm).source =
        {x : E3 | Real.exp (-r) < ‖x‖ ∧ ‖x‖ < Real.exp r} := by
  have hs (b : OpenPartialHomeomorph E3 M) (hb : ball 0 (Real.exp r) ⊆ b.source) :
      (b.restrOpen (ball 0 (Real.exp r)) isOpen_ball).source = ball 0 (Real.exp r) :=
    inter_eq_right.mpr hb
  have ht₁ : (b₁.restrOpen (ball 0 (Real.exp r)) isOpen_ball).target =
      b₁ '' ball 0 (Real.exp r) := by
    rw [← OpenPartialHomeomorph.image_source_eq_target, hs b₁ hs₁]
    rfl
  ext x
  rw [OpenPartialHomeomorph.trans_source, hs b₀ hs₀,
    OpenPartialHomeomorph.symm_source, ht₁]
  change (x ∈ ball 0 (Real.exp r) ∧ b₀ x ∈ b₁ '' ball 0 (Real.exp r)) ↔ _
  constructor
  · rintro ⟨hx, hi⟩
    exact ⟨(mem_matching_ball_overlap_iff b₀ b₁ hr hs₀ hs₁ hintersection hmatch hx).mp hi,
      mem_ball_zero_iff.mp hx⟩
  · rintro ⟨hlo, hhi⟩
    have hx := mem_ball_zero_iff.mpr hhi
    exact ⟨hx, (mem_matching_ball_overlap_iff b₀ b₁ hr hs₀ hs₁ hintersection hmatch hx).mpr hlo⟩

end Poincare
