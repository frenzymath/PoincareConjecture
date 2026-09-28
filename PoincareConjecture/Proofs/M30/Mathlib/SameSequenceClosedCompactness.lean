import PoincareConjecture.Proofs.M30.Mathlib.EventualClosedCompactness
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
















set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M30





theorem exists_smooth_limit_on_closed_convex_of_eventually_of_pointwise
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y]
    {Ω : Set X} (hclosed : IsClosed Ω) (hconvex : Convex ℝ Ω)
    (hne : (interior Ω).Nonempty) (f : ℕ → X → Y) (g : X → Y)
    (hf : ∀ᶠ k : ℕ in atTop, ContDiffOn ℝ ∞ (f k) Ω)
    (hbound : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop, ∀ x ∈ K,
        ‖iteratedFDerivWithin ℝ m (f k) Ω x‖ ≤ B)
    (hpoint : ∀ x ∈ interior Ω,
      Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ∃ F : X → Y, ContDiffOn ℝ ∞ F Ω ∧ EqOn F g (interior Ω) ∧
      ∀ m K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m (f k) Ω)
        (iteratedFDerivWithin ℝ m F Ω) atTop K := by
  classical
  have hzero (a : ℕ → ℕ) (H : X → Y)
      (hjets : ∀ K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ 0 (f (a k)) Ω)
        (iteratedFDerivWithin ℝ 0 H Ω) atTop K) :
      ∀ x ∈ Ω, Tendsto (fun k => f (a k) x) atTop (𝓝 (H x)) := by
    intro x hx
    have hz : TendstoUniformlyOn (fun k => f (a k)) H atTop {x} := by
      simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using
        (ContinuousMultilinearMap.uniformContinuous_eval_const
          (0 : Fin 0 → X)).comp_tendstoUniformlyOn
          (hjets {x} isCompact_singleton (singleton_subset_iff.mpr hx))
    exact hz.tendsto_at (mem_singleton x)
  have hidentify (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (H : X → Y)
      (hjets : ∀ K, IsCompact K → K ⊆ Ω → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ 0 (f (a k)) Ω)
        (iteratedFDerivWithin ℝ 0 H Ω) atTop K) :
      EqOn H g (interior Ω) := by
    intro x hx
    exact tendsto_nhds_unique (hzero a H hjets x (interior_subset hx))
      ((hpoint x hx).comp ha)
  obtain ⟨σ, hσ, F, hF, hFjets⟩ :=
    exists_smooth_subsequence_on_closed_convex_of_eventually
      hclosed hconvex hne f hf hbound
  have hFg : EqOn F g (interior Ω) :=
    hidentify σ hσ.tendsto_atTop F (fun K hK hKΩ => hFjets 0 K hK hKΩ)
  have hclosure : closure (interior Ω) = Ω :=
    (hconvex.closure_interior_eq_closure_of_nonempty_interior hne).trans hclosed.closure_eq
  refine ⟨F, hF, hFg, ?_⟩
  intro m K hK hKΩ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  by_contra hbadEvent
  obtain ⟨ns, hns, hbad⟩ :=
    Filter.exists_seq_forall_of_frequently (Filter.not_eventually.mp hbadEvent)
  obtain ⟨τ, hτ, G, hG, hGjets⟩ :=
    exists_smooth_subsequence_on_closed_convex_of_eventually
      hclosed hconvex hne (fun k => f (ns k)) (hns.eventually hf) (by
        intro C hC hCΩ j
        obtain ⟨B, hB, hevent⟩ := hbound C hC hCΩ j
        exact ⟨B, hB, hns.eventually hevent⟩)
  have hGg : EqOn G g (interior Ω) :=
    hidentify (fun k => ns (τ k)) (hns.comp hτ.tendsto_atTop) G
      (fun C hC hCΩ => hGjets 0 C hC hCΩ)
  have hGF : EqOn G F Ω :=
    (hGg.trans hFg.symm).of_subset_closure hG.continuousOn hF.continuousOn
      interior_subset hclosure.symm.subset
  have hconv := (hGjets m K hK hKΩ).congr_right
    ((hGF.iteratedFDerivWithin (𝕜 := ℝ) m).mono hKΩ)
  obtain ⟨j, hj⟩ := (Metric.tendstoUniformlyOn_iff.mp hconv ε hε).exists
  exact hbad (τ j) hj

end PoincareConjecture.M30
