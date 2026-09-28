import PoincareConjecture.Proofs.M30.Thm1_34.LocalVolume
import Mathlib.Topology.Order.IsLUB

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M30

open RiemannianMetric

theorem exists_buffered_local_geometry_parameters
    (n : ℕ) (A rho v K : ℝ) (hn : 1 ≤ n) (hA : 0 < A)
    (hrho : 0 < rho) (hv : 0 < v) (hK : 0 ≤ K) :
    ∃ r S delta vlower Vupper : ℕ → ℝ,
      (∀ j, 0 < r j) ∧ (∀ j, 0 < delta j) ∧
      (∀ j, 0 < vlower j) ∧ (∀ j, 0 ≤ Vupper j) ∧
      (∀ j, r j + 2 * delta j ≤ S j) ∧ (∀ j, S j < A) ∧
      (∀ b : ℝ, b < A → ∃ j : ℕ, b < r j) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [MeasurableSpace M] [BorelSpace M] [T3Space M]
        [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M],
      ∀ (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M),
        IsCompact (closure (g.ball p (3 * A + 2 * rho))) →
        (∀ x ∈ g.ball p (3 * A + 2 * rho), D.curvatureTensorNorm x ≤ K) →
        ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p rho) →
        ∀ j : ℕ,
          IsCompact (closure (g.ball p (S j))) ∧
          (∀ x ∈ g.ball p (S j), D.curvatureTensorNorm x ≤ K) ∧
          (∀ q ∈ g.ball p (r j),
            ENNReal.ofReal (vlower j) ≤ g.volumeMeasure (g.ball q (delta j))) ∧
          g.volumeMeasure (g.ball p (S j)) ≤ ENNReal.ofReal (Vupper j) := by
  obtain ⟨r, _, hr, hrlim⟩ := exists_seq_strictMono_tendsto' hA
  let S (j : ℕ) := (A + r j) / 2
  let delta (j : ℕ) := (A - r j) / 4
  let vlower (j : ℕ) := smallerBallVolumeBound n K (A + rho) v (delta j)
  have hdelta (j : ℕ) : 0 < delta j := div_pos (sub_pos.mpr (hr j).2) (by norm_num)
  have hdeltaL (j : ℕ) : delta j ≤ A + rho := by
    dsimp [delta]
    have := (hr j).1
    linarith
  have hSA (j : ℕ) : S j < A := by
    dsimp [S]
    linarith [(hr j).2]
  refine ⟨r, S, delta, vlower, fun _ => modelVolume n K A,
    fun j => (hr j).1, hdelta,
    fun j => smallerBallVolumeBound_pos hn hK (add_pos hA hrho) hv (hdelta j),
    fun _ => (modelVolume_pos hn hK hA).le, ?_, hSA, ?_, ?_⟩
  · intro j
    dsimp [S, delta]
    linarith
  · intro b hb
    exact (hrlim.eventually (lt_mem_nhds hb)).exists
  · intro M _ _ _ _ _ _ _ g D p hcompact hcurv hbase
    have hAH : A < 3 * A + 2 * rho := by linarith
    have hupper : g.volumeMeasure (g.ball p A) ≤
        ENNReal.ofReal (modelVolume n K A) := by
      apply volume_upper_of_precompact_ball g p hn (hA.trans hAH) hK hcompact D
        (fun x hx w => D.ricci_quadratic_lower_bound_of_curvatureTensorNorm_le
          x (hcurv x hx) w) hA hAH
    intro j
    have hsubA : g.ball p (S j) ⊆ g.ball p A :=
      fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal (hSA j).le)
    have hsubH : g.ball p (S j) ⊆ g.ball p (3 * A + 2 * rho) :=
      fun _ hx => hx.trans_le (ENNReal.ofReal_le_ofReal ((hSA j).trans hAH).le)
    refine ⟨hcompact.of_isClosed_subset isClosed_closure (closure_mono hsubH),
      fun x hx => hcurv x (hsubH hx), ?_, (measure_mono hsubA).trans hupper⟩
    intro q hq
    exact ((local_volume_bounds_of_base_volume g D p hn hA hrho hv hK
      hcompact hcurv hbase (hdelta j) (hdeltaL j)).2 q
        (hq.trans_le (ENNReal.ofReal_le_ofReal (hr j).2.le))).1

end PoincareConjecture.M30
