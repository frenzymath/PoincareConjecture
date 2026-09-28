import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiProper
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology ContDiff SchwartzMap ComplexConjugate

namespace Complex

private def derivativeEquiv (f : ℂ → ℂ)
    (hbij : ∀ z, Function.Bijective (fderiv ℝ f z)) (z : ℂ) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ f z)
    (LinearMap.ker_eq_bot.mpr (hbij z).1) (LinearMap.range_eq_top.mpr (hbij z).2)

private theorem derivativeEquiv_coe (f : ℂ → ℂ)
    (hbij : ∀ z, Function.Bijective (fderiv ℝ f z)) (z : ℂ) :
    (derivativeEquiv f hbij z : ℂ →L[ℝ] ℂ) = fderiv ℝ f z :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

private theorem exists_homeomorph_of_proper_local (f : ℂ → ℂ)
    (hproper : IsProperMap f) (hlocal : IsLocalHomeomorph f) :
    ∃ e : ℂ ≃ₜ ℂ, (e : ℂ → ℂ) = f := by
  have hfiber (y : ℂ) : (f ⁻¹' {y}).Finite := by
    apply (hproper.isCompact_preimage isCompact_singleton).finite
    apply IsDiscrete.of_openPartialHomeomorph f Subset.rfl
    intro x _
    obtain ⟨e, hx, he⟩ := hlocal x
    exact ⟨e, hx, he.symm⟩
  have hcover : IsCoveringMap f :=
    isCoveringMap_iff_isCoveringMapOn_univ.mpr
      (hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
        (fun y _ => hfiber y) hlocal.isLocalHomeomorphOn)
  obtain ⟨g, hg, _⟩ := hcover.existsUnique_continuousMap_lifts
    (ContinuousMap.id ℂ) (f 0) 0 rfl
  have hright : f ∘ g = id := hg.2
  have hleft : (g : ℂ → ℂ) ∘ f = id := by
    apply hcover.eq_of_comp_eq (g.continuous.comp hproper.continuous) continuous_id
      (a := (0 : ℂ))
    · funext z
      exact congrFun hright (f z)
    · exact hg.1
  refine ⟨{ toFun := f
            invFun := g
            left_inv := fun z => congrFun hleft z
            right_inv := fun z => congrFun hright z
            continuous_toFun := hproper.continuous
            continuous_invFun := g.continuous }, rfl⟩

theorem exists_smooth_homeomorph_of_proper_nondegenerate (f : ℂ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hproper : IsProperMap f)
    (hbij : ∀ z, Function.Bijective (fderiv ℝ f z)) :
    ∃ e : ℂ ≃ₜ ℂ, (e : ℂ → ℂ) = f ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) := by
  have hD (z : ℂ) : HasFDerivAt f (derivativeEquiv f hbij z : ℂ →L[ℝ] ℂ) z := by
    rw [derivativeEquiv_coe]
    exact (hf.differentiable (by simp) z).hasFDerivAt
  have hlocal : IsLocalHomeomorph f := by
    intro z
    exact ⟨hf.contDiffAt.toOpenPartialHomeomorph f (hD z) (by simp),
      hf.contDiffAt.mem_toOpenPartialHomeomorph_source (hD z) (by simp), rfl⟩
  obtain ⟨e, he⟩ := exists_homeomorph_of_proper_local f hproper hlocal
  refine ⟨e, he, ?_⟩
  apply e.contDiff_symm (f₀' := derivativeEquiv f hbij)
  · simpa only [he] using hD
  · simpa only [he] using hf

theorem exists_smooth_beltrami_diffeomorphism (μ : 𝓢(ℂ, ℂ))
    (hμ : HasCompactSupport (μ : ℂ → ℂ)) {k : ℝ} (hk : k < 1)
    (hbound : ∀ z, ‖μ z‖ ≤ k) :
    ∃ e : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (e : ℂ → ℂ) ∧ ContDiff ℝ ∞ (e.symm : ℂ → ℂ) ∧
      Tendsto (fderiv ℝ (e : ℂ → ℂ)) (cocompact ℂ) (𝓝 (ContinuousLinearMap.id ℝ ℂ)) ∧
      ∀ z, fderiv ℝ (e : ℂ → ℂ) z 1 + I * fderiv ℝ (e : ℂ → ℂ) z I =
        μ z * (fderiv ℝ (e : ℂ → ℂ) z 1 - I * fderiv ℝ (e : ℂ → ℂ) z I) := by
  obtain ⟨f, hf, hproper, hlim, hbij, heq⟩ :=
    exists_proper_nondegenerate_beltrami_map μ hμ hk hbound
  obtain ⟨e, he, hinverse⟩ := exists_smooth_homeomorph_of_proper_nondegenerate f hf hproper hbij
  refine ⟨e, ?_, hinverse, ?_, ?_⟩
  · simpa only [he] using hf
  · simpa only [he] using hlim
  · simpa only [he] using heq

end Complex
