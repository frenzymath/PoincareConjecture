import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.Packing
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Extraction.Radial
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.LengthLimit













noncomputable section
set_option autoImplicit false

open Set Filter Topology
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : ℕ → Type}
  [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
  [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
  [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]




theorem exists_subseq_proper_pointed_limit_of_ricci_lower_bound
    (g : ∀ j, RiemannianMetric n (M j)) (p : ∀ j, M j)
    (hn : 1 ≤ n) (κ : ℝ) (hκ : 0 ≤ κ)
    (hcomplete : ∀ j, MetricComplete (g j))
    (D : ∀ j, LeviCivitaData (g j))
    (hRic : ∀ j x v,
      -(((n : ℝ) - 1) * κ) * (g j).inner x v v ≤ (D j).ricci x v v) :
    let X := fun k => (g k).toBasedMetricSpace (p k)
    letI (k : ℕ) : CompleteSpace (X k).carrier :=
      (g k).completeSpace_toMetricSpace (hcomplete k)
    ∃ hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ k m,
      m ∈ packingAdmissible (X k).base δ R → m ≤ N,
    ∃ phi : ℕ → ℕ,
      ∃ S : CompatiblePointedCompactSystem.{0},
        StrictMono phi ∧
          ProperSpace S.completedLimit.carrier ∧
          (∀ i, Metric.ball (S.stage (i + 1)).base (i : ℝ) ⊆
            Set.range (S.transition i)) ∧
          (∀ i, ∃ R : VaryingRealizationSequence
              (fun j => ((uniformPackingBoundedClosedBall X hpack (phi j) i)
                |>.toFiniteDiameterBasedMetricSpace).toBasedMetricSpaceBundle)
              ((S.stage i).toFiniteDiameterBasedMetricSpace
                |>.toBasedMetricSpaceBundle),
            Tendsto
                (fun j => @Metric.hausdorffDist (R.ambient j).carrier
                  inferInstance (Set.range (R.left j)) (Set.range (R.right j)))
                atTop (𝓝 0) ∧
              PointedGHConverges
                (fun j => (uniformPackingBoundedClosedBall X hpack (phi j) i)
                  |>.toFiniteDiameterBasedMetricSpace)
                (S.stage i).toFiniteDiameterBasedMetricSpace) := by
  dsimp
  letI (j : ℕ) : MetricSpace (M j) := (g j).toMetricSpace
  letI (j : ℕ) : CompleteSpace (M j) :=
    (g j).completeSpace_toMetricSpace (hcomplete j)
  let X : ℕ → BasedMetricSpaceBundle :=
    fun j => (g j).toBasedMetricSpace (p j)
  letI (j : ℕ) : CompleteSpace (X j).carrier :=
    (g j).completeSpace_toMetricSpace (hcomplete j)
  have hpack : ∀ δ R, 0 < δ → ∃ N : ℕ, ∀ k m,
      m ∈ packingAdmissible (X k).base δ R → m ≤ N := by
    intro δ R hδ
    let N : ℕ := ⌈modelVolume n κ (3 * max R 1) /
      modelVolume n κ (min (δ / 2) (max R 1) / 2)⌉₊
    refine ⟨N, ?_⟩
    intro k m hm
    exact packing_card_le_of_ricci_lower_bound (g k) (p k) hn hδ hκ
      (hcomplete k) (D k) (fun x v => hRic k x v) hm
  obtain ⟨phi, S, hphi, hproper, hinner, hreal⟩ :=
    exists_subseq_compatible_marked_closedBall_limits_with_proper_completedLimit_of_uniform_packing_bounds
      X hpack
  refine ⟨hpack, phi, S, hphi, hproper, hinner, hreal⟩





theorem exists_subseq_proper_geodesic_pointed_limit_of_ricci_lower_bound
    (g : ∀ j, RiemannianMetric n (M j)) (p : ∀ j, M j)
    (hn : 1 ≤ n) (κ : ℝ) (hκ : 0 ≤ κ)
    (hcomplete : ∀ j, MetricComplete (g j))
    (D : ∀ j, LeviCivitaData (g j))
    (hRic : ∀ j x v,
      -(((n : ℝ) - 1) * κ) * (g j).inner x v v ≤ (D j).ricci x v v) :
    ∃ phi : ℕ → ℕ, ∃ S : CompatiblePointedCompactSystem.{0},
      StrictMono phi ∧ ProperSpace S.completedLimit.carrier ∧
      (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
        γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y) ∧
      PointedGHConvergesUnbounded
        (fun j => (g (phi j)).toBasedMetricSpace (p (phi j))) S.completedLimit := by
  let X : ℕ → BasedMetricSpaceBundle := fun j => (g j).toBasedMetricSpace (p j)
  letI (j : ℕ) : CompleteSpace (X j).carrier :=
    (g j).completeSpace_toMetricSpace (hcomplete j)
  obtain ⟨hpack, phi, S, hphi, hproper, hinner, hreal⟩ :=
    exists_subseq_proper_pointed_limit_of_ricci_lower_bound g p hn κ hκ hcomplete D hRic
  have happrox : ∀ j, ∀ x y : (X j).carrier, ∀ r ε : ℝ,
      0 < r → 0 < ε → r < dist x y →
        ∃ z, dist x z = r ∧ dist z y < dist x y - r + ε := by
    intro j x y r ε hr hε
    exact (g j).approximate_split_toMetricSpace x y hr hε
  have hreals : ∀ i, Nonempty (VaryingRealizationSequence
      (fun j => ((uniformPackingBoundedClosedBall X hpack (phi j) i)
        |>.toFiniteDiameterBasedMetricSpace).toBasedMetricSpaceBundle)
      (S.stage i).toFiniteDiameterBasedMetricSpace.toBasedMetricSpaceBundle) := by
    intro i
    obtain ⟨R, _⟩ := hreal i
    exact ⟨R⟩
  have hcover := S.radial_stage_coverage_of_inner_ball_range hinner
  letI : ProperSpace S.completedLimit.carrier := hproper
  refine ⟨phi, S, hphi, hproper, ?_, ?_⟩
  · exact S.completedLimit_is_geodesic_of_exact_splitting
      (CompatiblePointedCompactSystem.completedLimit_exact_split_of_approximate_splits
        X hpack happrox phi S hcover hreals)
  · exact CompatiblePointedCompactSystem.pointedGHConvergesUnbounded_of_approximate_splits
      X hpack happrox phi S hcover hreals

end PoincareConjecture.RiemannianMetric

