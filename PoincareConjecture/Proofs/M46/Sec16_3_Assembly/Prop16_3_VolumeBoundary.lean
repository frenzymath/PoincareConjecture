import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Precompact
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M46

theorem canonical_modelVolume_mono {n : ℕ} {K r s : ℝ}
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hrs : r ≤ s) :
    RiemannianMetric.modelVolume n K r ≤ RiemannianMetric.modelVolume n K s := by
  unfold RiemannianMetric.modelVolume
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Nat.cast_nonneg n) (RiemannianMetric.euclideanUnitBallVolume_nonneg n))
  exact intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) hr hrs
    ((ae_restrict_mem measurableSet_Ioc).mono fun t ht =>
      pow_nonneg (RiemannianMetric.modelS_nonneg hK ht.1.le) _)
    (RiemannianMetric.intervalIntegrable_modelS_pow n K 0 s)

theorem canonical_smallBall_volume_at_boundary
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n) {R K s : ℝ}
    (hK : 0 ≤ K) (hs : 0 < s) (hsR : s ≤ R)
    (hcompact : IsCompact (closure (g.ball p R))) (D : LeviCivitaData g)
    (hRic : ∀ x ∈ g.ball p R, ∀ v : TangentSpace (𝓡 n) x,
      -(((n : ℝ) - 1) * K) * g.inner x v v ≤ D.ricci x v v) :
    (ENNReal.ofReal (RiemannianMetric.modelVolume n K s) /
        ENNReal.ofReal (RiemannianMetric.modelVolume n K R)) *
      g.volumeMeasure (g.ball p R) ≤ g.volumeMeasure (g.ball p s) := by
  have hR := hs.trans_le hsR
  rcases hsR.eq_or_lt with hsame | hsR
  · subst R
    have hpos := ENNReal.ofReal_pos.mpr (RiemannianMetric.modelVolume_pos hn hK hs)
    rw [ENNReal.div_self hpos.ne' ENNReal.ofReal_ne_top, one_mul]
  let u : ℕ → ℝ := fun j => R - (R - s) / ((j : ℝ) + 1)
  have hu (j : ℕ) : s ≤ u j ∧ u j < R := by
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hdiv : (R - s) / ((j : ℝ) + 1) ≤ R - s := by
      apply (div_le_iff₀ hj).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
    have hdivpos := div_pos (sub_pos.mpr hsR) hj
    constructor <;> dsimp [u] <;> linarith
  have humono : Monotone u := by
    intro j k hjk
    have hcast : (j : ℝ) ≤ k := by exact_mod_cast hjk
    have hdiv := div_le_div_of_nonneg_left (sub_nonneg.mpr hsR.le)
      (by positivity : (0 : ℝ) < (j : ℝ) + 1) (by linarith : (j : ℝ) + 1 ≤ k + 1)
    dsimp [u]
    linarith
  have hutend : Tendsto u atTop (𝓝 R) := by
    have h := (tendsto_const_nhds (x := R)).sub
      ((tendsto_const_nhds (x := R - s)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa only [mul_zero, sub_zero, one_div, ← div_eq_mul_inv] using h
  have hballs : Monotone (fun j => g.ball p (u j)) := by
    intro j k hjk x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (humono hjk))
  have hunion : (⋃ j, g.ball p (u j)) = g.ball p R := by
    ext x
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, hx⟩
      exact hx.trans_le (ENNReal.ofReal_le_ofReal (hu j).2.le)
    · intro hx
      have hlt : g.edist p x < ENNReal.ofReal R := hx
      have hevent := ((ENNReal.continuous_ofReal.tendsto R).comp hutend).eventually
        (Ioi_mem_nhds hlt)
      obtain ⟨j, hj⟩ := hevent.exists
      exact mem_iUnion.mpr ⟨j, hj⟩
  rw [← hunion, hballs.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro j
  have hcompare := g.smallBall_volume_lower_bound_of_precompact_ball p hn hR hK
    hcompact D hRic hs (hu j).1 (hu j).2
  apply le_trans _ hcompare
  apply mul_le_mul' _ le_rfl
  apply ENNReal.div_le_div_left
  exact ENNReal.ofReal_le_ofReal
    (canonical_modelVolume_mono hK (hs.le.trans (hu j).1) (hu j).2.le)

end PoincareConjecture.Proofs.M46
