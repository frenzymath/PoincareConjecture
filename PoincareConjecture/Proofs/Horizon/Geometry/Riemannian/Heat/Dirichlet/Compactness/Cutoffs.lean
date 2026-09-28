import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.Compact










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem exists_finite_chart_cutoffs {K : Set M} (hK : IsCompact K) :
    ∃ (s : Finset M) (χ : M → M → ℝ),
      (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (χ i)) ∧
      (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) i).source) ∧
      (∀ i x, χ i x ∈ Icc (0 : ℝ) 1) ∧
      ∀ x ∈ K, ∃ i ∈ s, χ i =ᶠ[𝓝 x] 1 := by
  classical
  let b (x : M) : SmoothBumpFunction (𝓡 n) x := Classical.choice inferInstance
  let U (x : M) := {y | (b x : M → ℝ) =ᶠ[𝓝 y] 1}
  have hU (x : M) : U x ∈ 𝓝 x := by
    exact eventually_eventually_nhds.mpr (b x).eventuallyEq_one
  obtain ⟨s, _, hs⟩ := hK.elim_nhds_subcover U (fun x _ => hU x)
  refine ⟨s, fun i => b i, fun i => (b i).contMDiff,
    fun i => (b i).hasCompactSupport, fun i => (b i).tsupport_subset_chartAt_source,
    fun i _ => (b i).mem_Icc, ?_⟩
  intro x hx
  obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp (hs hx)
  exact ⟨i, hi, hix⟩


theorem exists_finite_chart_partition {K : Set M} (hK : IsCompact K) :
    ∃ (s : Finset M) (ρ : SmoothPartitionOfUnity s (𝓡 n) M K),
      (∀ i, HasCompactSupport (ρ i : M → ℝ)) ∧
      ∀ i, tsupport (ρ i : M → ℝ) ⊆
        (chartAt (EuclideanSpace ℝ (Fin n)) (i : M)).source := by
  classical
  obtain ⟨s, χ, hχ, hχc, hχs, hχ01, hχone⟩ := exists_finite_chart_cutoffs (n := n) hK
  let b : BumpCovering s M K :=
    { toFun := fun i => ⟨χ i, (hχ i).continuous⟩
      locallyFinite' := locallyFinite_of_finite _
      nonneg' := fun i x => (hχ01 i x).1
      le_one' := fun i x => (hχ01 i x).2
      eventuallyEq_one' := fun x hx => by
        obtain ⟨i, hi, hix⟩ := hχone x hx
        exact ⟨⟨i, hi⟩, hix⟩ }
  let ρ := b.toSmoothPartitionOfUnity (fun i => hχ i)
  have hs (i : s) : tsupport (ρ i : M → ℝ) ⊆ tsupport (χ i) :=
    closure_mono (b.support_toPartitionOfUnity_subset i)
  exact ⟨s, ρ,
    fun i => (hχc i).of_isClosed_subset (isClosed_tsupport (ρ i : M → ℝ)) (hs i),
    fun i => (hs i).trans (hχs i)⟩

end PoincareConjecture.LeviCivitaData.Dirichlet
