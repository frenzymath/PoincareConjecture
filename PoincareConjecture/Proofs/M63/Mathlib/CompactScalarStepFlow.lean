import PoincareConjecture.Proofs.M03.Existence.CompactTimeDependentFlowNative
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped ContDiff Bundle

theorem exists_contDiff_scalar_local_flow_on_compact
    {k : ℕ∞} (hk : k ≠ 0) (Y : ℝ → ℝ → ℝ)
    (hY : ContDiff ℝ k (Function.uncurry Y))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ K ⊆ U ∧
      ∃ ε > 0, ∃ f : (ℝ × ℝ) × ℝ → ℝ,
        (∀ p ∈ U, f (p, 0) = p.2) ∧
        (∀ p ∈ U, ∀ u ∈ Ioo (-ε) ε,
          HasDerivAt (fun r => f (p, r)) (Y (p.1 + u) (f (p, u))) u) ∧
        ContDiffOn ℝ k f (U ×ˢ Ioo (-ε) ε) := by
  let V : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) p :=
    fun p => (1, Y p.1 p.2)
  have hV : ContMDiff 𝓘(ℝ, ℝ × ℝ)
      (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, ℝ × ℝ)) k
      (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    exact contDiff_const.prodMk hY
  obtain ⟨U, hU, hKU, ε, hε, α, hzero, hcurve, hsmooth⟩ :=
    PoincareConjecture.CompactTimeDependentFlowNative.exists_contDiff_local_flow_on_compact
      hk V hV hK
  have hd (p : ℝ × ℝ) (hp : p ∈ U) (u : ℝ) (hu : u ∈ Ioo (-ε) ε) :
      HasDerivAt (fun r => α (p, r)) (1, Y (α (p, u)).1 (α (p, u)).2) u := by
    have hmf := (hcurve p hp u hu).hasMFDerivAt (Ioo_mem_nhds hu.1 hu.2)
    have hv := hmf.hasFDerivAt.hasDerivAt
    change HasDerivAt (fun r => α (p, r))
      ((1 : ℝ) • (1, Y (α (p, u)).1 (α (p, u)).2)) u at hv
    simpa only [one_smul] using hv
  have hd1 (p : ℝ × ℝ) (hp : p ∈ U) (u : ℝ) (hu : u ∈ Ioo (-ε) ε) :
      HasDerivAt (fun r => (α (p, r)).1) 1 u :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt u (hd p hp u hu)
  have htime (p : ℝ × ℝ) (hp : p ∈ U) :
      EqOn (fun u => (α (p, u)).1) (fun u => p.1 + u) (Ioo (-ε) ε) := by
    have ha (u : ℝ) : HasDerivAt (fun r => p.1 + r) 1 u :=
      (hasDerivAt_id u).const_add p.1
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-ε) ε).isPreconnected
      (fun u hu => (hd1 p hp u hu).differentiableAt.differentiableWithinAt)
      (fun u _ => (ha u).differentiableAt.differentiableWithinAt)
      (fun u hu => (hd1 p hp u hu).deriv.trans (ha u).deriv.symm)
      (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨neg_lt_zero.mpr hε, hε⟩)
    simp only [hzero p hp, add_zero]
  refine ⟨U, hU, hKU, ε, hε, fun z => (α z).2, ?_, ?_, ?_⟩
  · intro p hp
    exact congrArg Prod.snd (hzero p hp)
  · intro p hp u hu
    have h : HasDerivAt (fun r => (α (p, r)).2)
        (Y (α (p, u)).1 (α (p, u)).2) u :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt u (hd p hp u hu)
    have ht : (α (p, u)).1 = p.1 + u := htime p hp hu
    rw [ht] at h
    exact h
  · rw [← modelWithCornersSelf_prod] at hsmooth
    rw [chartedSpaceSelf_prod] at hsmooth
    exact hsmooth.contDiffOn.snd
