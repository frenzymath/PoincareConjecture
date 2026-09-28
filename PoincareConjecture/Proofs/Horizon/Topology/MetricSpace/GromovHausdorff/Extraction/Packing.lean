import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Packing.Compactness
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Extraction.Marked

open Set Filter Topology
open scoped Topology NNReal ENNReal lp

noncomputable section

namespace Poincare.GromovHausdorff

theorem exists_subseq_marked_closedBall_realizations_of_uniform_packing_bounds
    (X : ℕ → BasedMetricSpaceBundle.{0})
    [∀ k, CompleteSpace (X k).carrier]
    (hpack : ∀ δ S, 0 < δ → ∃ N : ℕ, ∀ k n,
      n ∈ packingAdmissible (X k).base δ S → n ≤ N) :
    ∃ φ : ℕ → ℕ, ∃ Y : ℕ → PointedCompactMetricSpace.{0},
      StrictMono φ ∧
      ∀ i, ∃ S : VaryingRealizationSequence
          (fun n =>
            (PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace
              (uniformPackingBoundedClosedBall X hpack (φ n) i)).toBasedMetricSpaceBundle)
          (PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace
            (Y i)).toBasedMetricSpaceBundle,
        Tendsto
          (fun n => @Metric.hausdorffDist (S.ambient n).carrier inferInstance
            (Set.range (S.left n)) (Set.range (S.right n)))
          atTop (𝓝 0) ∧
      PointedGHConverges
          (fun n =>
            PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace
              (uniformPackingBoundedClosedBall X hpack (φ n) i))
          (PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace (Y i)) := by
  obtain ⟨p, φ₀, hφ₀, hgh⟩ :=
    exists_subseq_tendsto_closedBallGHSpace_of_uniform_packing_bounds X hpack
  let A : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{0} :=
    fun i n =>
      PointedCompactMetricSpace.toFiniteDiameterBasedMetricSpace
        (uniformPackingBoundedClosedBall X hpack (φ₀ n) i)
  letI : ∀ i n, CompactSpace (A i n).carrier := by
    intro i n
    change CompactSpace
      (uniformPackingBoundedClosedBall X hpack (φ₀ n) i).carrier
    infer_instance
  have hbounded : ∀ i, UniformlyBoundedDiameter (A i) := by
    intro i
    refine ⟨2 * (i : ℝ), ?_⟩
    intro n x y
    calc
      dist
          (x : (uniformPackingBoundedClosedBall X hpack (φ₀ n) i).carrier)
          (y : (uniformPackingBoundedClosedBall X hpack (φ₀ n) i).carrier) ≤
          Metric.diam (Set.univ : Set
            (uniformPackingBoundedClosedBall X hpack (φ₀ n) i).carrier) :=
        Metric.dist_le_diam_of_mem Metric.isBounded_of_compactSpace
          (Set.mem_univ _) (Set.mem_univ _)
      _ ≤ 2 * (i : ℝ) :=
        packingBoundedClosedBall_diam_le
          (X (φ₀ n)) (i : ℝ) (Nat.cast_nonneg i)
          (packingBound_at_of_uniform_packing_bounds X hpack (φ₀ n))
  have hghA : ∀ i, Tendsto
      (fun n => _root_.GromovHausdorff.toGHSpace (A i n).carrier)
      atTop (𝓝 (p i)) := by
    intro i
    change Tendsto
      (fun n => _root_.GromovHausdorff.toGHSpace
        (uniformPackingBoundedClosedBall X hpack (φ₀ n) i).carrier)
      atTop (𝓝 (p i))
    exact hgh i
  obtain ⟨ψ, Y, hψ, _hcarrier, hreal⟩ :=
    exists_common_subseq_marked_realizations A hbounded p hghA
  refine ⟨fun n => φ₀ (ψ n), Y, hφ₀.comp hψ, ?_⟩
  intro i
  obtain ⟨S, hS, hpointed⟩ := hreal i
  refine ⟨S, ?_, ?_⟩
  · simpa [A, Function.comp_def] using hS
  · simpa [A, Function.comp_def] using hpointed

end Poincare.GromovHausdorff
