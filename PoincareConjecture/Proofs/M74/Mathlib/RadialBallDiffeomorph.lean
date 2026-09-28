import PoincareConjecture.Proofs.M74.Mathlib.IncreasingRadiusChart
import PoincareConjecture.Proofs.M74.Mathlib.SphereNormalize

set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M74

noncomputable def radiusVector (f : ℝ → ℝ) (x : StandardCapSpace) : StandardCapSpace :=
  (f ‖x‖ / ‖x‖) • x

@[simp] theorem radiusVector_zero (f : ℝ → ℝ) : radiusVector f 0 = 0 := by
  simp [radiusVector]

theorem radiusVector_norm (f : ℝ → ℝ) {x : StandardCapSpace} (hx : x ≠ 0)
    (hf : 0 < f ‖x‖) : ‖radiusVector f x‖ = f ‖x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [radiusVector, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hf hn)]
  exact div_mul_cancel₀ _ (ne_of_gt hn)

theorem radiusVector_left (f g : ℝ → ℝ) {x : StandardCapSpace} (hx : x ≠ 0)
    (hf : 0 < f ‖x‖) (hgf : g (f ‖x‖) = ‖x‖) :
    radiusVector g (radiusVector f x) = x := by
  change (g ‖radiusVector f x‖ / ‖radiusVector f x‖) • radiusVector f x = x
  rw [radiusVector_norm f hx hf, hgf, radiusVector, smul_smul]
  have hscalar : (‖x‖ / f ‖x‖) * (f ‖x‖ / ‖x‖) = 1 := by
    field_simp [ne_of_gt hf, norm_ne_zero_iff.mpr hx]
  rw [hscalar, one_smul]

theorem radiusVector_linear {f : ℝ → ℝ} {k ε : ℝ}
    (hlin : ∀ r ∈ Ioo (0 : ℝ) ε, f r = k * r) {x : StandardCapSpace}
    (hx : ‖x‖ < ε) : radiusVector f x = k • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [radiusVector, hlin _ ⟨norm_pos_iff.mpr hx0, hx⟩,
      mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hx0)]

theorem radiusVector_contDiffAt {f : ℝ → ℝ} {x : StandardCapSpace}
    (hx : x ≠ 0) (hf : ContDiffAt ℝ ∞ f ‖x‖) :
    ContDiffAt ℝ ∞ (radiusVector f) x := by
  have hn : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => ‖y‖) x := contDiffAt_norm ℝ hx
  exact ((hf.comp x hn).div hn (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

theorem radiusVector_contDiffAt_zero {f : ℝ → ℝ} {k ε : ℝ} (hε : 0 < ε)
    (hlin : ∀ r ∈ Ioo (0 : ℝ) ε, f r = k * r) :
    ContDiffAt ℝ ∞ (radiusVector f) (0 : StandardCapSpace) := by
  apply (show ContDiffAt ℝ ∞ (fun x : StandardCapSpace => k • x) 0 from
    contDiffAt_id.const_smul k).congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε : (0 : StandardCapSpace) ∈ ball 0 ε)]
    with x hx
  exact radiusVector_linear hlin (mem_ball_zero_iff.mp hx)

private theorem radius_inverse_linear (e : OpenPartialHomeomorph ℝ ℝ) {R ε k : ℝ}
    (hsource : e.source = Ioo 0 R) (hεR : ε ≤ R) (hk : 0 < k)
    (hlin : ∀ r ∈ Ioo (0 : ℝ) ε, e r = k * r) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) (k * ε)) : e.symm r = k⁻¹ * r := by
  have hdiv : r / k ∈ Ioo (0 : ℝ) ε :=
    ⟨div_pos hr.1 hk, (div_lt_iff₀ hk).mpr (by nlinarith [hr.2])⟩
  have hsrc : r / k ∈ e.source := by rw [hsource]; exact ⟨hdiv.1, hdiv.2.trans_le hεR⟩
  have heq : e (r / k) = r := by
    rw [hlin _ hdiv]
    field_simp
  have h := e.left_inv hsrc
  rw [heq] at h
  simpa only [div_eq_inv_mul] using h

noncomputable def radialBallDiffeomorph (e : OpenPartialHomeomorph ℝ ℝ) {R ε k : ℝ}
    (hsource : e.source = Ioo 0 R) (htarget : e.target = Ioi 0)
    (hf : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hε : 0 < ε) (hεR : ε ≤ R) (hk : 0 < k)
    (hlin : ∀ r ∈ Ioo (0 : ℝ) ε, e r = k * r) :
    Diffeomorph (𝓡 3) (𝓡 3)
      (⟨ball (0 : StandardCapSpace) R, isOpen_ball⟩ : TopologicalSpace.Opens StandardCapSpace)
      StandardCapSpace ∞ := by
  let U : TopologicalSpace.Opens StandardCapSpace := ⟨ball 0 R, isOpen_ball⟩
  have hR : 0 < R := hε.trans_le hεR
  have hsrc {x : StandardCapSpace} (hx : x ≠ 0) (hxR : x ∈ ball 0 R) :
      ‖x‖ ∈ e.source := by
    rw [hsource]
    exact ⟨norm_pos_iff.mpr hx, mem_ball_zero_iff.mp hxR⟩
  have hpos {x : StandardCapSpace} (hx : x ≠ 0) (hxR : x ∈ ball 0 R) :
      0 < e ‖x‖ := by
    have h := e.map_source (hsrc hx hxR)
    rwa [htarget] at h
  have hinv {y : StandardCapSpace} (hy : y ≠ 0) : e.symm ‖y‖ ∈ Ioo (0 : ℝ) R := by
    have hyt : ‖y‖ ∈ e.target := by rw [htarget]; exact norm_pos_iff.mpr hy
    have h := e.map_target hyt
    rwa [hsource] at h
  have hFinv (y : StandardCapSpace) : radiusVector e.symm y ∈ ball (0 : StandardCapSpace) R := by
    by_cases hy : y = 0
    · simp [hy, hR]
    · rw [mem_ball_zero_iff, radiusVector_norm e.symm hy (hinv hy).1]
      exact (hinv hy).2
  let F : StandardCapSpace → U := fun y => ⟨radiusVector e.symm y, hFinv y⟩
  refine {
    toFun := fun x => radiusVector e x.1
    invFun := F
    left_inv := ?_
    right_inv := ?_
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · intro x
    apply Subtype.ext
    change radiusVector e.symm (radiusVector e x.1) = x.1
    by_cases hx : x.1 = 0
    · simp [hx]
    · exact radiusVector_left e e.symm hx (hpos hx x.2) (e.left_inv (hsrc hx x.2))
  · intro y
    change radiusVector e (radiusVector e.symm y) = y
    by_cases hy : y = 0
    · simp [hy]
    · have hyt : ‖y‖ ∈ e.target := by rw [htarget]; exact norm_pos_iff.mpr hy
      exact radiusVector_left e.symm e hy (hinv hy).1 (e.right_inv hyt)
  · intro x
    change ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun x : U => radiusVector e x.1) x
    apply contMDiffAt_subtype_iff.mpr
    apply ContDiffAt.contMDiffAt
    by_cases hx : x.1 = 0
    · rw [hx]
      exact radiusVector_contDiffAt_zero hε hlin
    · exact radiusVector_contDiffAt hx (hf.contDiffAt (e.open_source.mem_nhds (hsrc hx x.2)))
  · apply (ContMDiff.subtypeVal_comp_iff U F).mp
    intro y
    apply ContDiffAt.contMDiffAt
    by_cases hy : y = 0
    · subst y
      exact radiusVector_contDiffAt_zero (mul_pos hk hε)
        (fun r hr => radius_inverse_linear e hsource hεR hk hlin hr)
    · have hyt : ‖y‖ ∈ e.target := by rw [htarget]; exact norm_pos_iff.mpr hy
      exact radiusVector_contDiffAt hy (hi.contDiffAt (e.open_target.mem_nhds hyt))

theorem radialBallDiffeomorph_apply (e : OpenPartialHomeomorph ℝ ℝ) {R ε k : ℝ}
    (hsource : e.source = Ioo 0 R) (htarget : e.target = Ioi 0)
    (hf : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hε : 0 < ε) (hεR : ε ≤ R) (hk : 0 < k)
    (hlin : ∀ r ∈ Ioo (0 : ℝ) ε, e r = k * r)
    (x : (⟨ball (0 : StandardCapSpace) R, isOpen_ball⟩ :
      TopologicalSpace.Opens StandardCapSpace)) :
    radialBallDiffeomorph e hsource htarget hf hi hε hεR hk hlin x = radiusVector e x.1 := rfl

end PoincareConjecture.M74
