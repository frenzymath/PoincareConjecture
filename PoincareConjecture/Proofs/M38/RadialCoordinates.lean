import PoincareConjecture.Proofs.M38.RadialProfile
import PoincareConjecture.Definitions.Ch12.StandardCap
import Mathlib.Analysis.InnerProductSpace.Calculus









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38


noncomputable def capRadialMap (f : ℝ → ℝ) (x : StandardCapSpace) : StandardCapSpace :=
  (f ‖x‖ / ‖x‖) • x


@[simp] theorem capRadialMap_zero (f : ℝ → ℝ) : capRadialMap f 0 = 0 := by
  simp [capRadialMap]



theorem capRadialMap_norm (f : ℝ → ℝ) (hf0 : f 0 = 0)
    (hf : ∀ t, 0 ≤ t → 0 ≤ f t) (x : StandardCapSpace) :
    ‖capRadialMap f x‖ = f ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, hf0]
  rw [capRadialMap, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (hf _ (norm_nonneg x)) (norm_nonneg x)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]



theorem capRadialMap_left_inverse (e : ℝ ≃o ℝ) (he0 : e 0 = 0) :
    Function.LeftInverse (capRadialMap e.symm) (capRadialMap e) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have he : ∀ t, 0 ≤ t → 0 ≤ e t := fun t ht => by
    simpa only [he0] using e.monotone ht
  have hpos : 0 < e ‖x‖ := by
    simpa only [he0] using e.strictMono (norm_pos_iff.mpr hx)
  rw [capRadialMap, capRadialMap_norm e he0 he, OrderIso.symm_apply_apply,
    capRadialMap, smul_smul]
  have hscalar : (‖x‖ / e ‖x‖) * (e ‖x‖ / ‖x‖) = 1 := by
    field_simp [hpos.ne', norm_ne_zero_iff.mpr hx]
  rw [hscalar, one_smul]


theorem capRadialMap_eq_smul (f : ℝ → ℝ) (c : ℝ) (x : StandardCapSpace)
    (h : f ‖x‖ = c * ‖x‖) : capRadialMap f x = c • x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [capRadialMap, h, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hx)]



theorem capRadialMap_smooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (a c : ℝ) (ha : 0 < a) (hlinear : ∀ t, t ≤ a → f t = c * t) :
    ContDiff ℝ ∞ (capRadialMap f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply ((contDiff_id.const_smul c :
      ContDiff ℝ ∞ (fun y : StandardCapSpace => c • y)).contDiffAt).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : StandardCapSpace) ha] with y hy
    exact capRadialMap_eq_smul f c y (hlinear _
      (show ‖y‖ < a by simpa only [Metric.mem_ball, dist_zero_right] using hy).le)
  · have hn : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => ‖y‖) x :=
      contDiffAt_norm ℝ hx
    exact ((hf.contDiffAt.comp x hn).div hn (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id


@[simp] theorem capRadialOrderIso_symm_zero {r c : ℝ} (hc : 0 < c) (hcr : c < r) :
    (capRadialOrderIso r c hc hcr).symm 0 = 0 := by
  apply (capRadialOrderIso r c hc hcr).injective
  simp


noncomputable def capRadialDiffeomorph (r c : ℝ) (hc : 0 < c) (hcr : c < r) :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ where
  toFun := capRadialMap (capRadialOrderIso r c hc hcr)
  invFun := capRadialMap (capRadialOrderIso r c hc hcr).symm
  left_inv := capRadialMap_left_inverse _ (by simp)
  right_inv := capRadialMap_left_inverse _ (capRadialOrderIso_symm_zero hc hcr)
  contMDiff_toFun := contMDiff_iff_contDiff.mpr
    (capRadialMap_smooth _ (capRadialProfile_smooth r c) (1 / 4) c (by norm_num)
      (fun t ht => capRadialProfile_linear r c t ht))
  contMDiff_invFun := contMDiff_iff_contDiff.mpr
    (capRadialMap_smooth _ (capRadialOrderIso_symm_smooth hc hcr) (c / 4) c⁻¹
      (by positivity) (fun t ht => by
        rw [capRadialOrderIso_symm_linear hc hcr t ht]
        exact div_eq_inv_mul t c))


theorem capRadialDiffeomorph_norm {r c : ℝ} (hc : 0 < c) (hcr : c < r)
    (x : StandardCapSpace) :
    ‖capRadialDiffeomorph r c hc hcr x‖ = capRadialProfile r c ‖x‖ := by
  apply capRadialMap_norm _ (by simp)
  intro t ht
  simpa using (capRadialProfile_strictMono hc hcr).monotone ht


theorem capRadialDiffeomorph_closedBall {r c : ℝ} (hc : 0 < c) (hcr : c < r) :
    capRadialDiffeomorph r c hc hcr '' Metric.closedBall 0 1 = Metric.closedBall 0 r := by
  ext y
  obtain ⟨x, rfl⟩ := (capRadialDiffeomorph r c hc hcr).surjective y
  change capRadialDiffeomorph r c hc hcr x ∈
    capRadialDiffeomorph r c hc hcr '' Metric.closedBall 0 1 ↔
    capRadialDiffeomorph r c hc hcr x ∈ Metric.closedBall 0 r
  have himage : capRadialDiffeomorph r c hc hcr x ∈
      capRadialDiffeomorph r c hc hcr '' Metric.closedBall 0 1 ↔
      x ∈ Metric.closedBall 0 1 := by
    constructor
    · rintro ⟨z, hz, heq⟩
      have hzx : z = x := (capRadialDiffeomorph r c hc hcr).injective heq
      exact hzx ▸ hz
    · exact Set.mem_image_of_mem _
  rw [himage]
  simp only [Metric.mem_closedBall, dist_zero_right, capRadialDiffeomorph_norm]
  simpa only [capRadialProfile_one] using
    ((capRadialProfile_strictMono hc hcr).le_iff_le (a := ‖x‖) (b := 1)).symm


theorem capRadialDiffeomorph_ball_two {r c : ℝ} (hc : 0 < c) (hcr : c < r) :
    capRadialDiffeomorph r c hc hcr '' Metric.ball 0 2 = Metric.ball 0 (r + c) := by
  ext y
  obtain ⟨x, rfl⟩ := (capRadialDiffeomorph r c hc hcr).surjective y
  change capRadialDiffeomorph r c hc hcr x ∈
    capRadialDiffeomorph r c hc hcr '' Metric.ball 0 2 ↔
    capRadialDiffeomorph r c hc hcr x ∈ Metric.ball 0 (r + c)
  have himage : capRadialDiffeomorph r c hc hcr x ∈
      capRadialDiffeomorph r c hc hcr '' Metric.ball 0 2 ↔ x ∈ Metric.ball 0 2 := by
    constructor
    · rintro ⟨z, hz, heq⟩
      have hzx : z = x := (capRadialDiffeomorph r c hc hcr).injective heq
      exact hzx ▸ hz
    · exact Set.mem_image_of_mem _
  rw [himage]
  simp only [Metric.mem_ball, dist_zero_right, capRadialDiffeomorph_norm]
  have htwo : capRadialProfile r c 2 = r + c := by
    rw [capRadialProfile_affine r c 2 (by norm_num)]
    ring
  rw [← htwo, (capRadialProfile_strictMono hc hcr).lt_iff_lt]



theorem capRadialDiffeomorph_smul {r c : ℝ} (hc : 0 < c) (hcr : c < r)
    (z : UnitTwoSphere) (t : ℝ) (ht : 1 / 2 ≤ t) :
    capRadialDiffeomorph r c hc hcr (t • z.val) = (r + c * (t - 1)) • z.val := by
  have htpos : 0 < t := by linarith
  have hz : ‖z.val‖ = 1 := by simp
  change (capRadialProfile r c ‖t • z.val‖ / ‖t • z.val‖) • (t • z.val) = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hz, mul_one,
    capRadialProfile_affine r c t ht, smul_smul, div_mul_cancel₀ _ htpos.ne']

end PoincareConjecture.M38
