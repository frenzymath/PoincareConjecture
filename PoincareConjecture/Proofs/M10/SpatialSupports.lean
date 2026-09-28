import PoincareConjecture.Proofs.M10.GradientNorm
import PoincareConjecture.Proofs.M10.LocalMetricBound
import PoincareConjecture.Statements.Ch06.ReducedLength









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem reducedLength_local_terminal_supports
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (z : M × ℝ) (hz : z ∈ univ ×ˢ Ioo 0 τmax) :
    ∃ N : Set (M × ℝ), IsOpen N ∧ z ∈ N ∧ N ⊆ univ ×ˢ Ioo 0 τmax ∧
      ∃ C D : ℝ≥0, ∀ w ∈ N, ∃ B : ReducedLengthUpperBarrier F T p w.1 w.2,
        |deriv (fun s ↦ B.representative (w.1, s)) w.2| ≤ D ∧
          ∀ v : TangentSpace (𝓡 n) w.1,
            |mvfderiv (𝓡 n) (fun q ↦ B.representative (q, w.2)) w.1 v| ≤
              C * (F.metric T).tangentNorm w.1 v := by
  obtain ⟨N, hNopen, hzN, hNtime, C, hC, hbarrier⟩ :=
    hDifferential.local_upper_barrier_bounds p z hz
  obtain ⟨V, hVopen, hzV, _, K, hK, hmetric⟩ :=
    slice_tangentNorm_locally_le_terminal (F := F) hwindow z hz
  refine ⟨N ∩ V, hNopen.inter hVopen, ⟨hzN, hzV⟩,
    fun w hw ↦ hNtime hw.1,
    ⟨Real.sqrt C * K, mul_nonneg (Real.sqrt_nonneg _) hK⟩, ⟨C, hC⟩, ?_⟩
  intro w hw
  obtain ⟨B, htime, hgradient, _⟩ := hbarrier w hw.1
  refine ⟨B, htime, fun v ↦ ?_⟩
  calc
    _ ≤ Real.sqrt C * (F.metric (T - w.2)).tangentNorm w.1 v :=
      abs_mvfderiv_le_of_gradientNormSq_le hgradient v
    _ ≤ Real.sqrt C * (K * (F.metric T).tangentNorm w.1 v) :=
      mul_le_mul_of_nonneg_left (hmetric w hw.2 v) (Real.sqrt_nonneg _)
    _ = (Real.sqrt C * K) * (F.metric T).tangentNorm w.1 v := (mul_assoc _ _ _).symm

end PoincareConjecture.M10
