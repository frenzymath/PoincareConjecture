import PoincareConjecture.Proofs.M10.LaplacianLinearity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [SecondCountableTopology M] [MeasurableSpace M]
  {g : RiemannianMetric n M}

theorem weak_comparison_of_local (D : LeviCivitaData g) (μ : Measure M) (u H : M → ℝ)
    (hlocal : ∀ q : M, ∃ U : Set M, IsOpen U ∧ q ∈ U ∧
      ∀ ψ : M → ℝ, ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ U → (∀ x, 0 ≤ ψ x) →
        Integrable (fun x ↦ ψ x * H x - u x * D.laplacian ψ x) μ ∧
        0 ≤ ∫ x, ψ x * H x - u x * D.laplacian ψ x ∂μ)
    (φ : M → ℝ) (hφ : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ φ)
    (hc : HasCompactSupport φ) (hpos : ∀ x, 0 ≤ φ x) :
    Integrable (fun x ↦ φ x * H x - u x * D.laplacian φ x) μ ∧
      0 ≤ ∫ x, φ x * H x - u x * D.laplacian φ x ∂μ := by
  classical
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (𝓡 n)
  choose U hU hq hweak using hlocal
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover U hU
    (fun q _ ↦ mem_iUnion.mpr ⟨q, hq q⟩)
  obtain ⟨θ, hθ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 n)
    (isClosed_tsupport φ) (fun i : s ↦ U i) (fun i ↦ hU i) (by
      intro q hq
      obtain ⟨i, hi, hqi⟩ := mem_iUnion₂.mp (hs hq)
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hqi⟩)
  let ψ : s → M → ℝ := fun i x ↦ θ i x * φ x
  have hψ (i : s) : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (ψ i) :=
    (θ i).contMDiff.mul hφ
  have htest (i : s) := hweak i (ψ i) (hψ i) (show HasCompactSupport (ψ i) from hc.mul_left)
    (tsupport_mul_subset_left.trans (hθ i)) (fun x ↦ mul_nonneg (θ.nonneg i x) (hpos x))
  have hsum (x : M) : (∑ i : s, ψ i x) = φ x := by
    by_cases hx : x ∈ tsupport φ
    · simp only [ψ, ← Finset.sum_mul, ← finsum_eq_sum_of_fintype, θ.sum_eq_one hx, one_mul]
    · simp only [ψ, image_eq_zero_of_notMem_tsupport hx, mul_zero, Finset.sum_const_zero]
  have hfun : (fun x ↦ ∑ i : s, ψ i x) = φ := funext hsum
  have hlap (x : M) : D.laplacian φ x = ∑ i : s, D.laplacian (ψ i) x := by
    rw [← hfun]
    exact laplacian_finsetSum_scalar D Finset.univ ψ
      (fun i _ ↦ (hψ i).of_le (by decide : (2 : ℕ∞ω) ≤ ∞)) x
  have heq (x : M) : φ x * H x - u x * D.laplacian φ x =
      ∑ i : s, (ψ i x * H x - u x * D.laplacian (ψ i) x) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hsum, hlap]
  constructor
  · simpa only [← heq] using integrable_finsetSum Finset.univ (fun i _ ↦ (htest i).1)
  · simp_rw [heq]
    rw [integral_finsetSum Finset.univ (fun i _ ↦ (htest i).1)]
    exact Finset.sum_nonneg (fun i _ ↦ (htest i).2)

end PoincareConjecture.M10
