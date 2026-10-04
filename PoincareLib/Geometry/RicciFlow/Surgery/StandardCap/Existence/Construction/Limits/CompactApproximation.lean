import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Basic.DoubleDerivativeBounds

/-!
# A selected compact approximation sequence for the supplied cap

Choose the compact flows once on their common closed time slab, then
choose all uniform covariant derivative bounds. The heights tend to
infinity in the original cap coordinates. This is the approximation
stage of Morgan-Tian Theorem 12.5, p. 297; see fixed-chart-endpoint.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff
open Set Filter

namespace PoincareMT.M34

/-- Heights greater than one tending to infinity for the compact-double
sequence (Theorem 12.5, p. 297). -/
def compactCapHeight (k : ℕ) : ℝ := (k : ℝ) + 2

/-- Every chosen height is in the actual double-construction range
(Theorem 12.5, p. 297). -/
theorem compactCapHeight_gt_one (k : ℕ) : 1 < compactCapHeight k := by
  dsimp [compactCapHeight]
  linarith [Nat.cast_nonneg (α := ℝ) k]

/-- The actual compact double at the k-th height
(Theorem 12.5, p. 297). -/
abbrev CompactCapDouble (g0 : StandardInitialMetric) (k : ℕ) :=
  EndDouble g0.cylindrical_end (compactCapHeight_gt_one k)

/-- Selected compact flows with all covariant curvature bounds, before
constructing any limiting noncompact flow (Theorem 12.5, p. 297). -/
structure CompactCapApproximation (g0 : StandardInitialMetric) where
  /-- The common included terminal time. -/
  time : ℝ
  /-- The common slab is nondegenerate. -/
  time_pos : 0 < time
  /-- The actual flows, selected independently of derivative order. -/
  flow (k : ℕ) : RicciFlow 3 (CompactCapDouble g0 k) (Icc 0 time)
  /-- Each flow starts at the actual glued metric. -/
  initial_metric (k : ℕ) :
    (flow k).metric 0 = endDoubleMetric g0.cylindrical_end (compactCapHeight_gt_one k)
  /-- One constant for each derivative order. -/
  curvature_bound : ℕ → ℝ
  /-- The constants can be taken positive. -/
  bound_pos (m : ℕ) : 0 < curvature_bound m
  /-- Bounds hold at all indices and included times, including time zero. -/
  curvature_le (m k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 time) (q : CompactCapDouble g0 k) :
    ((flow k).connection t).curvatureDerivativeNorm m q ≤ curvature_bound m

/-- The predecessor services construct the entire approximation sequence
for every supplied initial metric (Theorem 12.5, p. 297). -/
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

/-- Every selected time slice is complete for its actual metric
(Theorem 12.5, p. 297). -/
theorem CompactCapApproximation.complete {g0 : StandardInitialMetric}
    (A : CompactCapApproximation g0) (k : ℕ) (t : ℝ) :
    MetricComplete ((A.flow k).metric t) :=
  ((A.flow k).metric t).metricComplete_of_compact

/-- The zeroth derivative bound is the full four-tensor curvature bound
(Theorem 12.5, p. 297). -/
theorem CompactCapApproximation.full_curvature_le {g0 : StandardInitialMetric}
    (A : CompactCapApproximation g0) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 A.time)
    (q : CompactCapDouble g0 k) :
    ((A.flow k).connection t).curvatureTensorNorm q ≤ A.curvature_bound 0 := by
  simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using A.curvature_le 0 k t ht q

/-- The fixed original-cap sources eventually contain every compact set
(Theorem 12.5, p. 297). -/
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

end PoincareMT.M34
