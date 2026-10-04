import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Ball.SeedBallChain
import PoincareLib.Geometry.Riemannian.Distance.SegmentLocality

/-!
# A uniformly finite spatial seed chain

The Uniform Seed argument of the September 20 complete-contract review
uses a path of fixed bounded length. A compact actual slice supplies a
constant-speed metric segment, and a uniform subdivision gives the same
positive volume coefficient before the path or flow is chosen.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.Proofs.M47

/-- A fixed subdivision count for paths of speed at most L and step
radius r, in the Uniform Seed spatial comparison. -/
noncomputable def seedChainSteps (L r : ℝ) : ℕ := Nat.ceil (L / r) + 1

/-- The subdivision always contains at least one interval. -/
theorem seedChainSteps_pos (L r : ℝ) : 0 < seedChainSteps L r :=
  Nat.succ_pos _

/-- The chosen subdivision has strictly smaller steps than the tested
radius, including the zero-speed case. -/
theorem seedChainSteps_size {L r : ℝ} (hr : 0 < r) :
    L / (seedChainSteps L r : ℝ) < r := by
  have hN : 0 < (seedChainSteps L r : ℝ) := Nat.cast_pos.mpr (seedChainSteps_pos L r)
  have hceil := Nat.le_ceil (L / r)
  have hlt : L / r < (seedChainSteps L r : ℝ) := by
    unfold seedChainSteps
    push_cast
    linarith
  exact (div_lt_iff₀ hN).mpr (by
    have h := (div_lt_iff₀ hr).mp hlt
    simpa only [mul_comm] using h)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

/-- A compact actual slice gives a path with the uniform distance bound
needed by the seed-chain subdivision, by local Hopf--Rinow. -/
theorem exists_seed_path_of_distance [T2Space M] [CompactSpace M]
    (g : RiemannianMetric 3 M) (x y : M) {L : ℝ} (hL : 0 < L)
    (hxy : g.edist x y < ENNReal.ofReal L) :
    ∃ gamma : ℝ → M, gamma 0 = x ∧ gamma 1 = y ∧
      MapsTo gamma (Icc 0 1) (g.ball x L) ∧ ContinuousOn gamma (Icc 0 1) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (gamma s) (gamma t) ≤ ENNReal.ofReal (L * |s - t|) := by
  obtain ⟨gamma, hzero, hone, hmaps, hdist⟩ :=
    g.exists_intrinsic_metric_segment_of_precompact_ball x y hL
      isClosed_closure.isCompact hxy
  have hfinite : g.edist x y ≠ ⊤ := ne_top_of_lt (hxy.trans_le le_top)
  refine ⟨gamma, hzero, hone, hmaps, g.continuousOn_of_edist_segment hfinite hdist, ?_⟩
  intro s hs t ht
  rw [hdist s hs t ht, mul_comm L, ENNReal.ofReal_mul (abs_nonneg _)]
  exact mul_le_mul' le_rfl hxy.le

/-- A bounded-speed path through controlled doubled balls transports
volume with a coefficient fixed by L,r,A,k, not by the path or events. -/
theorem seed_path_volume_transport [T3Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (gamma : ℝ → M) {A L r k : ℝ}
    (hA : 0 < A) (hr : 0 < r) (hk : 0 < k)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (gamma s) (gamma t) ≤ ENNReal.ofReal (L * |s - t|))
    (hcompact : ∀ s ∈ Icc (0 : ℝ) 1, IsCompact (closure (g.ball (gamma s) (2 * r))))
    (hcurv : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ g.ball (gamma s) (2 * r),
      D.curvatureTensorNorm z ≤ (A / (2 * r)) ^ 2)
    (hvolume : ENNReal.ofReal (k * r ^ 3) ≤ calibratedMetricVolume g (g.ball (gamma 0) r)) :
    ENNReal.ofReal (seedBallStepLoss A ^ seedChainSteps L r * k * r ^ 3) ≤
      calibratedMetricVolume g (g.ball (gamma 1) r) := by
  let N := seedChainSteps L r
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (seedChainSteps_pos L r)
  let centers : ℕ → M := fun n => gamma ((n : ℝ) / N)
  have hmem (n : ℕ) (hn : n ≤ N) : (n : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
    exact ⟨div_nonneg (Nat.cast_nonneg _) hN.le,
      (div_le_one hN).mpr (Nat.cast_le.mpr hn)⟩
  have hstep (n : ℕ) (hn : n < N) :
      g.edist (centers (n + 1)) (centers n) < ENNReal.ofReal r := by
    have h := hspeed _ (hmem (n + 1) hn) _ (hmem n hn.le)
    have hdiff : |((n + 1 : ℕ) : ℝ) / N - (n : ℝ) / N| = 1 / N := by
      rw [Nat.cast_add, Nat.cast_one, add_div, add_sub_cancel_left,
        abs_of_pos (div_pos zero_lt_one hN)]
    rw [hdiff] at h
    exact h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by
      simpa only [mul_one_div] using seedChainSteps_size (L := L) hr))
  have h := seed_ball_volume_chain g D centers N hA hr hk hstep
    (fun n hn => hcompact _ (hmem (n + 1) hn))
    (fun n hn => hcurv _ (hmem (n + 1) hn))
    (by simpa only [centers, Nat.cast_zero, zero_div] using hvolume)
  simpa only [centers, div_self hN.ne', N] using h

end PoincareMT.Proofs.M47
