import PoincareConjecture.Proofs.M11.IntervalFamily
import Mathlib.Analysis.Calculus.MeanValue





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem interval_function_smoothOn (I : SpacetimeInterval)
    {f : (smoothInterval I).Point → E} {g : ℝ → E}
    (hf : ContMDiff (𝓡∂ 1) 𝓘(ℝ, E) ∞ f)
    (hg : ∀ t : (smoothInterval I).Point, g t.val = f t) :
    ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ g I.domain := by
  let := intervalChartedSpace I
  have h := interval_family_smoothOn (J := 𝓘(ℝ)) I
    (f := fun p : (smoothInterval I).Point × ℝ ↦ f p.1)
    (g := fun p : ℝ × ℝ ↦ g p.1) (hf.comp contMDiff_fst) (fun t _ ↦ hg t)
  exact h.comp (contMDiff_id.prodMk (contMDiff_const (c := (0 : ℝ)))).contMDiffOn
    (fun _ ht ↦ ⟨ht, mem_univ _⟩)

theorem interval_constant_of_derivative_zero (I : SpacetimeInterval)
    {f : (smoothInterval I).Point → E}
    (hf : ContMDiff (𝓡∂ 1) 𝓘(ℝ, E) ∞ f)
    (hz : ∀ t, mfderiv (𝓡∂ 1) 𝓘(ℝ, E) f t
      ((smoothInterval I).positiveTangent t) = 0)
    (s t : (smoothInterval I).Point) : f s = f t := by
  classical
  let := intervalChartedSpace I
  let g : ℝ → E := fun r ↦ if hr : r ∈ I.domain then f ⟨r, hr⟩ else 0
  have hg (r : (smoothInterval I).Point) : g r.val = f r := by
    dsimp [g]
    rw [dif_pos r.property]
  have hgs := interval_function_smoothOn I hf hg
  have hgz (r : ℝ) (hr : r ∈ I.domain) : fderivWithin ℝ g I.domain r = 0 := by
    let q : (smoothInterval I).Point := ⟨r, hr⟩
    have hc := mfderivWithin_comp (I := 𝓡∂ 1) (I' := 𝓘(ℝ))
      (I'' := 𝓘(ℝ, E)) (s := univ) (u := I.domain) q
      ((hgs r hr).mdifferentiableWithinAt (by simp))
      (((smoothInterval I).inclusion_smooth q).mdifferentiableAt (by simp)).mdifferentiableWithinAt
      (fun p _ ↦ p.property) (uniqueMDiffWithinAt_univ (𝓡∂ 1))
    have he : g ∘ (Subtype.val : (smoothInterval I).Point → ℝ) = f := funext hg
    simp only [mfderivWithin_univ, mfderivWithin_eq_fderivWithin] at hc
    have h := congrArg (fun L ↦ L ((smoothInterval I).positiveTangent q)) hc
    have hn : mfderiv (𝓡∂ 1) 𝓘(ℝ)
        (Subtype.val : (smoothInterval I).Point → ℝ) q
        ((smoothInterval I).positiveTangent q) = 1 := by
      rw [← (smoothInterval I).inclusionDerivative_eq]
      exact ((smoothInterval I).inclusionDerivative q).apply_symm_apply 1
    change mfderiv (𝓡∂ 1) 𝓘(ℝ, E) (g ∘ Subtype.val) q
        ((smoothInterval I).positiveTangent q) =
      fderivWithin ℝ g I.domain r (mfderiv (𝓡∂ 1) 𝓘(ℝ)
        (Subtype.val : (smoothInterval I).Point → ℝ) q
        ((smoothInterval I).positiveTangent q)) at h
    rw [he, hn, hz q] at h
    exact ContinuousLinearMap.ext_ring h.symm
  rw [← hg s, ← hg t]
  exact (interval_convex I).is_const_of_fderivWithin_eq_zero
    (fun r hr ↦ ((hgs r hr).mdifferentiableWithinAt (by simp)).differentiableWithinAt)
    hgz s.property t.property

end PoincareConjecture.Proofs.M11
