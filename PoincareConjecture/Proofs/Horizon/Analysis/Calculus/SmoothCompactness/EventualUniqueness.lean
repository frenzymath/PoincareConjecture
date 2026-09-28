import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Eventual








set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis.Calculus



theorem tendstoUniformlyOn_iteratedFDeriv_of_locallyEventuallyContDiff
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y]
    {Ω : Set X} (hΩ : IsOpen Ω) {f : ℕ → X → Y} {F : X → Y}
    (hpoint : ∀ x ∈ Ω, Tendsto (fun k => f k x) atTop (𝓝 (F x)))
    (hsmooth : LocallyEventuallyContDiff Ω f)
    (hbound : ∀ K, IsCompact K → K ⊆ Ω →
      ∀ m : ℕ, ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m (f k) x‖ ≤ B)
    (m : ℕ) {K : Set X} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (f k))
      (iteratedFDeriv ℝ m F) atTop K := by
  let fs := fun k => UniformFun.ofFun (fun x : K => iteratedFDeriv ℝ m (f k) x)
  let Fs := UniformFun.ofFun (fun x : K => iteratedFDeriv ℝ m F x)
  have ht : Tendsto fs atTop (𝓝 Fs) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨σ, hσ, G, hG, hjet⟩ :=
      exists_smoothSubsequenceExtraction_finiteDimensional_of_locallyEventuallyContDiff
        hΩ (fun k => f (ns k))
        (fun A hA hAΩ => hns.eventually (hsmooth A hA hAΩ))
        (fun A hA hAΩ l => by
          obtain ⟨B, hB⟩ := hbound A hA hAΩ l
          exact ⟨B, hns.eventually hB⟩)
    have heq : EqOn G F Ω := by
      intro x hx
      have hz := (ContinuousMultilinearMap.uniformContinuous_eval_const
        (0 : Fin 0 → X)).comp_tendstoUniformlyOn
          (hjet 0 {x} isCompact_singleton (singleton_subset_iff.mpr hx))
      have hp : Tendsto (fun k => f (ns (σ k)) x) atTop (𝓝 (G x)) := by
        simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
          hz.tendsto_at (mem_singleton x)
      exact tendsto_nhds_unique hp ((hpoint x hx).comp (hns.comp hσ.tendsto_atTop))
    have hjetEq : EqOn (iteratedFDeriv ℝ m G) (iteratedFDeriv ℝ m F) K := by
      intro x hx
      have hnear : G =ᶠ[𝓝 x] F :=
        Filter.eventuallyEq_of_mem (hΩ.mem_nhds (hKΩ hx)) (fun y hy => heq hy)
      exact (hnear.iteratedFDeriv ℝ m).self_of_nhds
    refine ⟨σ, UniformFun.tendsto_iff_tendstoUniformly.mpr ?_⟩
    exact tendstoUniformlyOn_iff_restrict.mp ((hjet m K hK hKΩ).congr_right hjetEq)
  exact tendstoUniformlyOn_iff_restrict.mpr (UniformFun.tendsto_iff_tendstoUniformly.mp ht)

end Poincare.Analysis.Calculus
