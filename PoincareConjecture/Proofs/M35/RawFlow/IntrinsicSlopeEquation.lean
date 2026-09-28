import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicEvolution
import PoincareConjecture.Proofs.M03.ScalarMixedDerivative










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

noncomputable def rawWarpingSlope (t s : ℝ) : ℝ :=
  deriv (rawWarpingRadius P G hrotation t) s

noncomputable def rawTangentialCurvature (t s : ℝ) : ℝ :=
  (1 - rawWarpingSlope P G hrotation t s ^ 2) /
    rawWarpingRadius P G hrotation t s ^ 2

theorem rawRadialVelocity_hasDerivAt {t s : ℝ} (ht : t ∈ Ico 0 G.lifetime)
    (hs : 0 < s) : HasDerivAt (rawRadialVelocity P G hrotation t)
      (2 * deriv (deriv (rawWarpingRadius P G hrotation t)) s /
        rawWarpingRadius P G hrotation t s) s := by
  rw [rawRadialVelocity_eq P G hrotation ht, rawWarpingRadius_eq P G hrotation ht,
    ← intrinsicRadialAcceleration_eq (G.flow.metric t) (hrotation t ht) (G.complete P ht) hs]
  exact intrinsicRadialVelocity_hasDerivAt (G.flow.metric t) (hrotation t ht)
    (G.complete P ht) s

theorem rawWarpingSlope_contDiff {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) :
    ContDiff ℝ ∞ (rawWarpingSlope P G hrotation t) := by
  change ContDiff ℝ ∞ (deriv (rawWarpingRadius P G hrotation t))
  rw [rawWarpingRadius_eq P G hrotation ht]
  exact (contDiff_infty_iff_deriv.mp
    (intrinsicWarpingRadius_contDiff (G.flow.metric t) (hrotation t ht) (G.complete P ht))).2

theorem rawWarpingSlope_contDiffOn :
    ContDiffOn ℝ ∞ (Function.uncurry (rawWarpingSlope P G hrotation))
      (Ioo 0 G.lifetime ×ˢ univ) := by
  change ContDiffOn ℝ ∞
    (fun z : ℝ × ℝ => deriv (rawWarpingRadius P G hrotation z.1) z.2) _
  have h := Proofs.M03.contDiffOn_fderiv_family isOpen_Ioo isOpen_univ
    (rawWarpingRadius P G hrotation) (rawWarpingRadius_contDiffOn P G hrotation)
  simpa only [fderiv_apply_one_eq_deriv, Function.uncurry, rawWarpingSlope] using
    h.clm_apply (contDiffOn_const (c := (1 : ℝ)))



theorem rawWarpingSlope_hasDerivAt_time {t s : ℝ}
    (ht : t ∈ Ioo 0 G.lifetime) (hs : 0 < s) :
    HasDerivAt (fun a => rawWarpingSlope P G hrotation a s)
      (deriv (deriv (rawWarpingSlope P G hrotation t)) s -
        rawRadialVelocity P G hrotation t s * deriv (rawWarpingSlope P G hrotation t) s +
        rawTangentialCurvature P G hrotation t s * rawWarpingSlope P G hrotation t s) t := by
  have htG : t ∈ Ico 0 G.lifetime := ⟨ht.1.le, ht.2⟩
  let f := rawWarpingRadius P G hrotation t
  let p := deriv f
  let v := rawRadialVelocity P G hrotation t
  have hf : ContDiff ℝ ∞ f := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation htG]
    exact intrinsicWarpingRadius_contDiff (G.flow.metric t) (hrotation t htG)
      (G.complete P htG)
  have hp : ContDiff ℝ ∞ p := (contDiff_infty_iff_deriv.mp hf).2
  have hpp : ContDiff ℝ ∞ (deriv p) := (contDiff_infty_iff_deriv.mp hp).2
  have hfn : f s ≠ 0 := by
    dsimp only [f]
    rw [rawWarpingRadius_eq P G hrotation htG]
    exact (intrinsicWarpingRadius_pos (G.flow.metric t) (hrotation t htG)
      (G.complete P htG) hs).ne'
  have hf' := (hf.differentiable (by simp) s).hasDerivAt
  have hp' := (hp.differentiable (by simp) s).hasDerivAt
  have hpp' := (hpp.differentiable (by simp) s).hasDerivAt
  have hv : HasDerivAt v (2 * deriv p s / f s) s :=
    rawRadialVelocity_hasDerivAt P G hrotation htG hs
  have hR := (hpp'.add (((hp'.pow 2).sub_const 1).div hf' hfn)).sub (hv.mul hp')
  change HasDerivAt (fun r => deriv p r + (p r ^ 2 - 1) / f r - v r * p r)
    (deriv (deriv p) s +
      ((2 : ℝ) * p s ^ (2 - 1) * deriv p s * f s - (p s ^ 2 - 1) * p s) / f s ^ 2 -
      (2 * deriv p s / f s * p s + v s * deriv p s)) s at hR
  have heq : (fun r => deriv (fun a => rawWarpingRadius P G hrotation a r) t) =ᶠ[𝓝 s]
      (fun r => deriv p r + (p r ^ 2 - 1) / f r - v r * p r) := by
    filter_upwards [eventually_gt_nhds hs] with r hr
    exact (rawWarpingRadius_hasDerivAt_time P G hrotation ht hr).deriv
  have hspace : deriv (fun r => deriv (fun a => rawWarpingRadius P G hrotation a r) t) s =
      deriv (deriv p) s - v s * deriv p s + ((1 - p s ^ 2) / f s ^ 2) * p s := by
    rw [heq.deriv_eq, hR.deriv]
    field_simp [hfn]
    ring
  have hm := Proofs.M03.hasDerivAt_fderiv_family isOpen_Ioo isOpen_univ
    (rawWarpingRadius P G hrotation) (rawWarpingRadius_contDiffOn P G hrotation)
    ht (mem_univ s)
  have hm' := hm.clm_apply (hasDerivAt_const t (1 : ℝ))
  simp only [map_zero, add_zero, fderiv_apply_one_eq_deriv] at hm'
  rw [hspace] at hm'
  exact hm'

end PoincareConjecture.M35.Uniqueness
