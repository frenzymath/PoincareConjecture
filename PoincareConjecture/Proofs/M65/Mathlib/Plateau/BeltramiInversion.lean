import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiUniqueness
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Field.Lemmas










set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology ContDiff ComplexConjugate

namespace Complex



def beltramiCircleInversion (z : ℂ) : ℂ := (conj z)⁻¹


@[simp] theorem beltramiCircleInversion_involutive (z : ℂ) :
    beltramiCircleInversion (beltramiCircleInversion z) = z := by
  simp only [beltramiCircleInversion, map_inv₀, conj_conj, inv_inv]


@[simp] theorem beltramiCircleInversion_eq_zero (z : ℂ) :
    beltramiCircleInversion z = 0 ↔ z = 0 := by
  simp only [beltramiCircleInversion, inv_eq_zero, map_eq_zero]


theorem contDiffAt_beltramiCircleInversion {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ beltramiCircleInversion z := by
  apply conjCLE.contDiff.contDiffAt.inv
  exact star_ne_zero.mpr hz



theorem beltramiCircleInversion_tendsto_zero :
    Tendsto beltramiCircleInversion (cocompact ℂ) (𝓝[≠] (0 : ℂ)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝[≠] (0 : ℂ)) := by
    simpa only [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded' (α := ℂ))
  exact hi.comp conjCLE.toHomeomorph.isClosedEmbedding.tendsto_cocompact



theorem beltramiCircleInversion_tendsto_infinity :
    Tendsto beltramiCircleInversion (𝓝[≠] (0 : ℂ)) (cocompact ℂ) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (𝓝[≠] (0 : ℂ)) (cocompact ℂ) := by
    simpa only [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_nhdsNE_zero (α := ℂ))
  have hh := conjCLE.toHomeomorph.isClosedEmbedding.tendsto_cocompact.comp hi
  convert! hh using 1
  funext z
  exact (map_inv₀ (starRingEnd ℂ) z).symm


def beltramiCircleReflect (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  beltramiCircleInversion (f (beltramiCircleInversion z))

private theorem reflect_continuous (f : ℂ ≃ₜ ℂ) (hf0 : f 0 = 0) :
    Continuous (beltramiCircleReflect f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    apply continuousAt_iff_punctured_nhds.mpr
    have hh := beltramiCircleInversion_tendsto_zero.mono_right nhdsWithin_le_nhds
    have hlim := hh.comp (f.isClosedEmbedding.tendsto_cocompact.comp
      beltramiCircleInversion_tendsto_infinity)
    have hr0 : beltramiCircleReflect f 0 = 0 := by
      simp only [beltramiCircleReflect, beltramiCircleInversion, map_zero, inv_zero, hf0]
    rw [hr0]
    exact hlim
  · have hn : f (beltramiCircleInversion z) ≠ 0 := by
      intro hh
      exact hz ((beltramiCircleInversion_eq_zero z).mp (f.injective (hh.trans hf0.symm)))
    have hfj : ContinuousAt (fun w => f (beltramiCircleInversion w)) z :=
      f.continuous.continuousAt.comp (contDiffAt_beltramiCircleInversion hz).continuousAt
    exact (contDiffAt_beltramiCircleInversion hn).continuousAt.comp
      (f := fun w => f (beltramiCircleInversion w)) hfj



def beltramiReflectedHomeomorph (f : ℂ ≃ₜ ℂ) (hf0 : f 0 = 0) : ℂ ≃ₜ ℂ where
  toFun := beltramiCircleReflect f
  invFun := beltramiCircleReflect f.symm
  left_inv z := by
    simp only [beltramiCircleReflect, beltramiCircleInversion_involutive, f.symm_apply_apply]
  right_inv z := by
    simp only [beltramiCircleReflect, beltramiCircleInversion_involutive, f.apply_symm_apply]
  continuous_toFun := reflect_continuous f hf0
  continuous_invFun := reflect_continuous f.symm (f.injective (by
    simpa only [f.apply_symm_apply] using hf0.symm))



theorem hasDerivAt_beltramiCircleReflect (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0)
    (hf : DifferentiableAt ℂ f (beltramiCircleInversion z))
    (hne : f (beltramiCircleInversion z) ≠ 0) :
    HasDerivAt (beltramiCircleReflect f)
      (conj (deriv f (beltramiCircleInversion z)) /
        (z ^ 2 * (conj (f (beltramiCircleInversion z))) ^ 2)) z := by
  have hh : HasDerivAt (fun y => conj (f (conj y)))
      (conj (deriv f (beltramiCircleInversion z))) z⁻¹ := by
    simpa only [Function.comp_def, beltramiCircleInversion, map_inv₀, conj_conj]
      using hf.hasDerivAt.conj_conj
  have hn : conj (f (conj z⁻¹)) ≠ 0 := by
    apply star_ne_zero.mpr
    simpa only [← map_inv₀, beltramiCircleInversion] using hne
  have hd := (hh.comp z (hasDerivAt_inv hz)).inv hn
  convert! hd using 1
  · funext y
    simp only [Pi.inv_apply, beltramiCircleReflect, beltramiCircleInversion,
      Function.comp_def, map_inv₀]
  · dsimp only [Function.comp_def]
    simp only [beltramiCircleInversion, ← map_inv₀, div_eq_mul_inv, mul_inv_rev, neg_mul]
    ring




theorem analyticAt_beltramiCircleReflect_zero (f : ℂ ≃ₜ ℂ) (hf0 : f 0 = 0)
    (hhol : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ (f : ℂ → ℂ) z) :
    AnalyticAt ℂ (beltramiCircleReflect f) 0 := by
  apply analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    _ (reflect_continuous f hf0).continuousAt
  filter_upwards [beltramiCircleInversion_tendsto_infinity.eventually hhol,
    self_mem_nhdsWithin] with z hz hzne
  have hne : z ≠ 0 := hzne
  apply (hasDerivAt_beltramiCircleReflect f hne hz _).differentiableAt
  intro hh
  exact hne ((beltramiCircleInversion_eq_zero z).mp (f.injective (hh.trans hf0.symm)))




theorem contDiff_beltramiCircleReflect (f : ℂ ≃ₜ ℂ) (hf0 : f 0 = 0)
    (hf : ContDiff ℝ ∞ (f : ℂ → ℂ))
    (hhol : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ (f : ℂ → ℂ) z) :
    ContDiff ℝ ∞ (beltramiCircleReflect f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    exact (analyticAt_beltramiCircleReflect_zero f hf0 hhol).contDiffAt.restrict_scalars ℝ
  · have hn : f (beltramiCircleInversion z) ≠ 0 := by
      intro hh
      exact hz ((beltramiCircleInversion_eq_zero z).mp (f.injective (hh.trans hf0.symm)))
    exact (contDiffAt_beltramiCircleInversion hn).comp z
      (hf.contDiffAt.comp z (contDiffAt_beltramiCircleInversion hz))

end Complex
