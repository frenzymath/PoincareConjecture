import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.NoPeriod
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PullbackCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.OrbitMargins













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_distinct_radial_loop_powers
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {s K : ℝ} (hs : 0 < s)
    (hsK : s ≤ Poincare.ODE.Jacobi.comparisonRadius K)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 s))
    (hbound : ∀ x ∈ Metric.ball 0 s, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x w) ∧
        g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x w) ≤ 3 * ‖w‖ / 2)
    (hgauss : ∀ x ∈ Metric.ball 0 s, ∀ w,
      g.pullbackCoefficients e x x w = inner ℝ x w)
    (hcurv : ∀ x ∈ Metric.ball 0 s, D.curvatureTensorNorm (e x) ≤ K)
    (hspeed : ∀ v ∈ Metric.ball 0 s, ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) ≤ ‖v‖)
    (N : ℕ) (hN : 0 < N) (v : EuclideanSpace ℝ (Fin n))
    (hv : v ≠ 0) (hreturn : e v = e 0)
    (hshort : ‖v‖ ≤ loopPowerThreshold s N) :
    ∃ y : Fin (N + 1) → EuclideanSpace ℝ (Fin n),
      Injective y ∧ ∀ i, e (y i) = e 0 ∧ ‖y i‖ ≤ 2 * (i : ℝ) * ‖v‖ := by
  let a := loopOrbitRadius s N
  let r := a / 2
  let δ := 2 * (N : ℝ) * ‖v‖
  have ha : 0 < a := loopOrbitRadius_pos hs N
  have hr : 0 < r := by dsimp [r]; positivity
  have hra : r < a := by dsimp [r]; linarith
  have hdom : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆
      Metric.ball 0 a := Metric.closedBall_subset_ball hra
  have hmargins := loopPowerThreshold_margins hs (norm_nonneg v) N hshort
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hvball : v ∈ Metric.ball 0 s := by
    rw [Metric.mem_ball, dist_zero_right]
    nlinarith [hmargins.1, norm_nonneg v]
  have hbij (x) (hx : x ∈ Metric.ball 0 s) :
      Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e x) :=
    g.bijective_mfderiv_of_tangentNorm_lower_bound x (fun w => (hbound x hx w).1)
  obtain ⟨y, hy0, hy1, hy, hsegments⟩ := exists_bounded_radial_loop_powers g he hbij
    (fun x hx w => (hbound x hx w).1) v hreturn (hspeed v hvball) N hN
    (by nlinarith [hmargins.1, norm_nonneg v])
  obtain ⟨d, hd, hdmem, hdproj, hd0, hdbound, hfree⟩ :=
    exists_smooth_radial_deck_motion g he hbij (fun x hx w => (hbound x hx w).1)
      hspeed ⟨v, hvball⟩ hreturn
  have hcontrol := deck_motion_iterates_controlled hd hdproj hdbound N hmargins.2
  have hstep := deck_motion_maps_loop_powers he hbij hN hmargins.1 hd.continuousOn
    hdmem hdproj hd0 y hy0 hy1 (fun i => (hy i).2) hsegments
  have hiter0 := loop_powers_eq_iterate d (fun i => (y i : EuclideanSpace ℝ (Fin n)))
    hy0 hstep
  obtain ⟨G, DG, hag, hGbound, hGgauss, _, hGcurv⟩ :=
    g.exists_uniform_pullback_extension_with_curvature D
      (r := s / 2) (by linarith) (by linarith) he hbound hgauss
  have hnumeric := loopPowerThreshold_orbit_energy hs (norm_nonneg v) N hshort
  have hδ : δ < r / 16 := hnumeric.1
  have henergy : (N : ℝ) * δ ^ 2 < (r / 16) ^ 2 := hnumeric.2
  have himage (i : ℕ) (hi : i ≤ N) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ Metric.ball 0 a) : ‖d^[i] x‖ < s / 4 := by
    have hb := (hcontrol i hi).2.2.2 x hx
    have hx' : ‖x‖ < a := by simpa using hx
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi
    have hmul := mul_le_mul_of_nonneg_right hp (add_nonneg (norm_nonneg x) (norm_nonneg v))
    have hstrict := mul_lt_mul_of_pos_left hx' (by positivity : 0 < (2 : ℝ) ^ N)
    have hcap := loopPowerThreshold_quarter_margin hs (norm_nonneg v) N hshort
    change (2 : ℝ) ^ N * (a + ‖v‖) < s / 4 at hcap
    nlinarith [norm_nonneg v]
  have hpoint (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 a) :
      x ∈ Metric.closedBall 0 (s / 2) := by
    have hxsmall := himage 0 (Nat.zero_le N) x hx
    simpa only [Function.iterate_zero, id_eq, Metric.mem_closedBall, dist_zero_right] using
      hxsmall.le.trans (by linarith : s / 4 ≤ s / 2)
  have hnoperiod (m : ℕ) (hm : 0 < m) (hmN : m ≤ N)
      (hperiod : EqOn (d^[m]) id (Metric.ball 0 a)) : False := by
    have henergy' : (m : ℝ) * δ ^ 2 < (r / 16) ^ 2 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hmN) (sq_nonneg δ)).trans_lt henergy
    apply false_of_short_finite_period G DG hGgauss (inner_zero_of_gauss hGgauss)
      hGbound hm (K := K) hr hδ henergy' d Metric.isOpen_ball hdom
    · intro i
      exact contMDiffOn_iff_contDiffOn.mpr (hcontrol i (by omega)).1
    · intro i
      have hiN : i.val ≤ N := by omega
      rw [hiter0 ⟨i.val, by omega⟩]
      exact (hy ⟨i.val, by omega⟩).2.trans
        (by dsimp [δ]; gcongr)
    · exact hperiod.mono hdom
    · intro x hx
      have hxU := (hcontrol 0 (Nat.zero_le N)).2.1 (hdom hx)
      have hb := hdbound x hxU
      have ht := norm_add_le (d x - v) v
      rw [sub_add_cancel] at ht
      dsimp [δ]
      nlinarith [norm_nonneg v]
    · intro x hx
      exact hfree hv x ((hcontrol 0 (Nat.zero_le N)).2.1 (hdom hx))
    · intro i x hx b c
      have hxa := hdom (Metric.ball_subset_closedBall hx)
      have hc := hcontrol i (by omega)
      have himem : d^[i.val] x ∈ Metric.closedBall 0 (s / 2) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (himage i (by omega) x hxa).le.trans (by linarith)
      apply inner_deck_motion_of_pullback G g
        ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds
          (Metric.closedBall_subset_ball (by linarith : s / 2 < s) himem))).mdifferentiableAt (by simp))
        ((hc.1.contDiffAt (Metric.isOpen_ball.mem_nhds hxa)).differentiableAt (by simp))
        (hc.2.2.1.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hxa))
        ((hag x (hpoint x hxa)).self_of_nhds) ((hag _ himem).self_of_nhds)
    · intro i x hx
      exact (himage i (by omega) x (hdom (Metric.ball_subset_closedBall hx))).le.trans
        (by linarith)
    · intro i x hx t ht
      have hxsmall := himage i (by omega) x (hdom (Metric.ball_subset_closedBall hx))
      have htbound : ‖t • d^[i.val] x‖ ≤ s / 4 := by
        rw [norm_smul, Real.norm_of_nonneg ht.1]
        exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans
          (by simpa using hxsmall.le)
      have htmem : t • d^[i.val] x ∈ Metric.closedBall 0 (s / 2) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact htbound.trans (by linarith)
      rw [hGcurv _ htmem]
      exact hcurv _ (Metric.closedBall_subset_ball (by linarith : s / 2 < s) htmem)
  refine ⟨fun i => y i, ?_, hy⟩
  exact injective_loop_powers_of_no_deck_period he hbij hN hmargins.1 ha hmargins.2
    hd hdmem hdproj hd0 hdbound hnoperiod y hy0 hy1 (fun i => (hy i).2) hsegments

end PoincareConjecture.RiemannianMetric
