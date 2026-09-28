import PoincareConjecture.Proofs.M34.Thm12_5_Existence.DoubleDerivativeBounds










set_option autoImplicit false

open scoped Manifold ContDiff
open Set Filter

namespace PoincareConjecture.M34



def compactCapHeight (k : ℕ) : ℝ := (k : ℝ) + 2



theorem compactCapHeight_gt_one (k : ℕ) : 1 < compactCapHeight k := by
  dsimp [compactCapHeight]
  linarith [Nat.cast_nonneg (α := ℝ) k]



abbrev CompactCapDouble (g0 : StandardInitialMetric) (k : ℕ) :=
  EndDouble g0.cylindrical_end (compactCapHeight_gt_one k)



structure CompactCapApproximation (g0 : StandardInitialMetric) where

  time : ℝ

  time_pos : 0 < time

  flow (k : ℕ) : RicciFlow 3 (CompactCapDouble g0 k) (Icc 0 time)

  initial_metric (k : ℕ) :
    (flow k).metric 0 = endDoubleMetric g0.cylindrical_end (compactCapHeight_gt_one k)

  curvature_bound : ℕ → ℝ

  bound_pos (m : ℕ) : 0 < curvature_bound m

  curvature_le (m k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 time) (q : CompactCapDouble g0 k) :
    ((flow k).connection t).curvatureDerivativeNorm m q ≤ curvature_bound m



theorem compactCapApproximation_exists (P : M34StandardCapPredecessors)
    (g0 : StandardInitialMetric) (E0 : StandardCapEstimate g0) :
    Nonempty (CompactCapApproximation g0) := by
  classical
  obtain ⟨T, B, hT, hB, hflows⟩ := exists_uniform_endDouble_flows P g0 E0
  choose F hinit _hcomplete hfull using
    fun k => hflows (compactCapHeight k) (compactCapHeight_gt_one k)
  choose C hC hderiv using
    fun m => endDouble_flow_curvatureDerivative_bounds P.curvature g0 E0 hT hB m
  exact ⟨{
    time := T
    time_pos := hT
    flow := F
    initial_metric := hinit
    curvature_bound := C
    bound_pos := hC
    curvature_le := fun m k => hderiv m (compactCapHeight k) (compactCapHeight_gt_one k)
      (F k) (hinit k) (hfull k) }⟩



theorem CompactCapApproximation.complete {g0 : StandardInitialMetric}
    (A : CompactCapApproximation g0) (k : ℕ) (t : ℝ) :
    MetricComplete ((A.flow k).metric t) :=
  ((A.flow k).metric t).metricComplete_of_compact



theorem CompactCapApproximation.full_curvature_le {g0 : StandardInitialMetric}
    (A : CompactCapApproximation g0) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 A.time)
    (q : CompactCapDouble g0 k) :
    ((A.flow k).connection t).curvatureTensorNorm q ≤ A.curvature_bound 0 := by
  simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using A.curvature_le 0 k t ht q



theorem eventually_compact_subset_double_source (g0 : StandardInitialMetric)
    {K : Set StandardCapSpace} (hK : IsCompact K) :
    ∀ᶠ k : ℕ in atTop, K ⊆ endTruncation g0.cylindrical_end (compactCapHeight k + 1) := by
  obtain ⟨L, _hL, hKL⟩ := endTruncation_contains_compact g0.cylindrical_end hK
  obtain ⟨N, hN⟩ := exists_nat_gt L
  filter_upwards [eventually_ge_atTop N] with k hk
  apply hKL.trans (endTruncation_mono g0.cylindrical_end ?_)
  have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
  dsimp [compactCapHeight]
  linarith

end PoincareConjecture.M34
