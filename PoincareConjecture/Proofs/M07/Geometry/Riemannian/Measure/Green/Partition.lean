import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite

set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [SigmaCompactSpace M]

theorem exists_finite_chart_decomposition {u : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u) (hc : HasCompactSupport u) :
    ∃ (s : Finset M) (w : M → M → ℝ),
      (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (w i)) ∧
      (∀ i, HasCompactSupport (w i)) ∧
      (∀ i, tsupport (w i) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) i).source) ∧
      ∀ x, ∑ i ∈ s, w i x = u x := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (𝓡 n) M
  have hfinite := ρ.locallyFinite.finite_nonempty_inter_compact hc.isCompact
  refine ⟨hfinite.toFinset, fun i x => ρ i x * u x,
    (fun i => (ρ i).contMDiff.mul hu), (fun _ => hc.mul_left),
    (fun i => tsupport_mul_subset_left.trans (hρ i)), ?_⟩
  intro x
  have hs : Function.support (fun i => ρ i x * u x) ⊆ hfinite.toFinset := by
    intro i hi
    apply hfinite.mem_toFinset.mpr
    refine ⟨x, ?_, subset_tsupport u ?_⟩
    · exact (mul_ne_zero_iff.mp hi).1
    · exact (mul_ne_zero_iff.mp hi).2
  rw [← finsum_eq_sum_of_support_subset _ hs, ← finsum_mul,
    ρ.sum_eq_one (mem_univ x), one_mul]

end PoincareConjecture
