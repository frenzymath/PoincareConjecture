import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.EventualUniqueness
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Manifold Topology

namespace Poincare.Manifold

open Poincare.Analysis.Calculus

theorem exists_smooth_subsequence_of_locallyEventuallyBounded_chart_derivatives
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [SecondCountableTopology M]
    (f : ℕ → M → ℝ)
    (hsmooth : ∀ a : M, LocallyEventuallyContDiff (extChartAt (𝓡 n) a).target
      (fun k => f k ∘ (extChartAt (𝓡 n) a).symm))
    (hbound : ∀ a : M, LocallyEventuallyBoundedDerivatives
      (extChartAt (𝓡 n) a).target (fun k => f k ∘ (extChartAt (𝓡 n) a).symm)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b : M → ℝ,
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ b ∧
      (∀ x, Tendsto (fun k => f (σ k) x) atTop (𝓝 (b x))) ∧
      ∀ (a : M) (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
        IsCompact K → K ⊆ (extChartAt (𝓡 n) a).target →
        TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (f (σ k) ∘ (extChartAt (𝓡 n) a).symm))
          (iteratedFDeriv ℝ m (b ∘ (extChartAt (𝓡 n) a).symm)) atTop K := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨id, strictMono_id, fun _ => 0, contMDiff_const,
      fun x => isEmptyElim x, fun a => isEmptyElim a⟩
  obtain ⟨S, hS, hcover⟩ := TopologicalSpace.countable_cover_nhds
    (fun x : M => extChartAt_source_mem_nhds (I := 𝓡 n) x)
  obtain ⟨a, ha⟩ := countable_iff_exists_subset_range.mp hS
  have hcover' (x : M) : ∃ i, x ∈ (extChartAt (𝓡 n) (a i)).source := by
    have hx : x ∈ ⋃ y ∈ S, (extChartAt (𝓡 n) y).source := hcover.symm ▸ mem_univ x
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
    obtain ⟨i, rfl⟩ := ha hy
    exact ⟨i, hxy⟩
  let c := fun i : ℕ => extChartAt (𝓡 n) (a i)
  obtain ⟨σ, hσ, u, hu, hjet⟩ :=
    exists_common_smoothSubsequenceExtraction_finiteDimensional_of_locallyEventuallyContDiff
      (X := fun _ => EuclideanSpace ℝ (Fin n)) (Y := fun _ => ℝ)
      (fun i => isOpen_extChartAt_target (a i))
      (fun i k => f k ∘ (c i).symm) (fun i => hsmooth (a i)) (fun i => hbound (a i))
  have hp (i : ℕ) (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ (c i).target) :
      Tendsto (fun k => f (σ k) ((c i).symm z)) atTop (𝓝 (u i z)) := by
    have he := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
        (hjet i 0 {z} isCompact_singleton (singleton_subset_iff.mpr hz))
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      he.tendsto_at (mem_singleton z)
  choose j hj using hcover'
  let b : M → ℝ := fun x => u (j x) (c (j x) x)
  have hbpoint (x : M) : Tendsto (fun k => f (σ k) x) atTop (𝓝 (b x)) := by
    have he := hp (j x) (c (j x) x) ((c (j x)).map_source (hj x))
    simpa only [(c (j x)).left_inv (hj x), b] using he
  have hbeq (i : ℕ) (x : M) (hx : x ∈ (c i).source) : b x = u i (c i x) := by
    have he := hp i (c i x) ((c i).map_source hx)
    rw [(c i).left_inv hx] at he
    exact tendsto_nhds_unique (hbpoint x) he
  have hbsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ b := by
    intro x
    have hx : x ∈ (c (j x)).source := hj x
    have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (c (j x)) x := by
      apply (contMDiffOn_extChartAt (I := 𝓡 n) (x := a (j x))).contMDiffAt
      simpa only [extChartAt_source] using extChartAt_source_mem_nhds' hx
    have huat : ContDiffAt ℝ ∞ (u (j x)) (c (j x) x) :=
      (hu (j x)).contDiffAt (extChartAt_target_mem_nhds' ((c (j x)).map_source hx))
    apply (huat.contMDiffAt.comp x hc).congr_of_eventuallyEq
    filter_upwards [extChartAt_source_mem_nhds' hx] with y hy
    exact hbeq (j x) y hy
  refine ⟨σ, hσ, b, hbsmooth, hbpoint, ?_⟩
  intro p m K hK hKp
  apply tendstoUniformlyOn_iteratedFDeriv_of_locallyEventuallyContDiff
    (isOpen_extChartAt_target p)
    (fun z _ => hbpoint ((extChartAt (𝓡 n) p).symm z))
    (fun A hA hAp => hσ.tendsto_atTop.eventually (hsmooth p A hA hAp))
    (fun A hA hAp l => ?_) m hK hKp
  obtain ⟨B, hB⟩ := hbound p A hA hAp l
  exact ⟨B, hσ.tendsto_atTop.eventually hB⟩

end Poincare.Manifold
