import PoincareConjecture.Proofs.M28.Mathlib.WithinSmoothCompactness
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

theorem tendstoUniformlyOn_iteratedFDerivWithin_of_eventually_smooth
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {S : Set E} [LocallyCompactSpace S]
    (hconv : Convex ℝ S) (hS : UniqueDiffOn ℝ S)
    {f : ℕ → E → F} {g : E → F}
    (hpoint : ∀ x ∈ S, Tendsto (fun k => f k x) atTop (𝓝 (g x)))
    (hsmooth : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) S)
    (hbound : ∀ K, IsCompact K → K ⊆ S → ∀ m : ℕ,
      ∃ B : ℝ, ∀ᶠ k in atTop, ∀ x ∈ K,
        ‖iteratedFDerivWithin ℝ m (f k) S x‖ ≤ B)
    (m : ℕ) {K : Set E} (hK : IsCompact K) (hKS : K ⊆ S) :
    TendstoUniformlyOn (fun k => iteratedFDerivWithin ℝ m (f k) S)
      (iteratedFDerivWithin ℝ m g S) atTop K := by
  let fs := fun k => UniformFun.ofFun (fun x : K => iteratedFDerivWithin ℝ m (f k) S x)
  let gs := UniformFun.ofFun (fun x : K => iteratedFDerivWithin ℝ m g S x)
  have ht : Tendsto fs atTop (𝓝 gs) := by
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hns.eventually hsmooth)
    have htail := hns.comp (tendsto_add_atTop_nat N)
    obtain ⟨σ, hσ, G, _, hjets⟩ :=
      exists_common_contDiffOn_subsequence_of_withinJet_bounds (fun _ : ℕ => S)
        (fun _ => hconv) (fun _ => hS) (fun _ k => f (ns (k + N)))
        (fun _ k => hN (k + N) (Nat.le_add_left N k)) (by
          intro _ C hC hCS r
          obtain ⟨B, hB⟩ := hbound C hC hCS r
          exact ⟨B, htail.eventually hB⟩)
    have heq : EqOn (G 0) g S := by
      intro x hx
      have hz := (hjets 0 0 {x} isCompact_singleton
        (singleton_subset_iff.mpr hx)).tendsto_at (mem_singleton x)
      have hv := (continuous_eval_const (0 : Fin 0 → E)).tendsto
        (iteratedFDerivWithin ℝ 0 (G 0) S x) |>.comp hz
      have hlimit : Tendsto (fun k => f (ns (σ k + N)) x) atTop (𝓝 (G 0 x)) := by
        simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using hv
      exact tendsto_nhds_unique hlimit
        ((hpoint x hx).comp (htail.comp hσ.tendsto_atTop))
    refine ⟨fun k => σ k + N, UniformFun.tendsto_iff_tendstoUniformly.mpr ?_⟩
    exact tendstoUniformlyOn_iff_restrict.mp
      ((hjets 0 m K hK hKS).congr_right ((heq.iteratedFDerivWithin m).mono hKS))
  exact tendstoUniformlyOn_iff_restrict.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp ht)
