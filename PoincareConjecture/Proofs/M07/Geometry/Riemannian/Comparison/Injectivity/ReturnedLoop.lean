import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.InverseRadius
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ExponentialRays

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hasFDerivAt_endpoint_chart
    {e : EuclideanSpace ℝ (Fin n) → M} {v : EuclideanSpace ℝ (Fin n)}
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e v) :
    HasFDerivAt (fun x => extChartAt (𝓡 n) (e v) (e x))
      (show EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) from
        mfderiv (𝓡 n) (𝓡 n) e v) v := by
  have hc := (contMDiffAt_extChartAt (I := 𝓡 n) (n := ∞) (x := e v)).mdifferentiableAt
    (by simp)
  have hd := (hc.comp v he).differentiableAt.hasFDerivAt
  apply hd.congr_fderiv
  have hchain := mfderiv_comp v hc he
  rw [mfderiv_eq_fderiv] at hchain
  apply ContinuousLinearMap.ext
  intro a
  have h := congrArg (fun A => A a) hchain
  have hid := congrArg (fun A => A (mfderiv (𝓡 n) (𝓡 n) e v a))
    (mfderiv_extChartAt_self (I := 𝓡 n) (x := e v))
  exact h.trans hid

theorem exponential_double_eq_zero_of_opposite_radial_velocities [T2Space M]
    (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    {v w : EuclideanSpace ℝ (Fin n)}
    (hv : 2 * ‖v‖ < R) (hw : ‖w‖ < R)
    (hgv : g.IsGeodesicOn (fun t : ℝ => e (t • v))
      {t : ℝ | t • v ∈ Metric.ball 0 R})
    (hgw : g.IsGeodesicOn (fun t : ℝ => e (t • w))
      {t : ℝ | t • w ∈ Metric.ball 0 R})
    (heq : e v = e w)
    (hvel : mfderiv (𝓡 n) (𝓡 n) e v v = -mfderiv (𝓡 n) (𝓡 n) e w w) :
    e ((2 : ℝ) • v) = e 0 := by
  have hvmem : v ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith [norm_nonneg v]
  have hwmem : w ∈ Metric.ball 0 R := by simpa using hw
  let γ : ℝ → M := fun t => e (t • v)
  let η : ℝ → M := fun t => e ((-1 * t + 2) • w)
  have hγ : g.IsGeodesicOn γ (Icc (1 : ℝ) 2) := by
    intro t ht
    apply hgv
    simp only [mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
    rw [norm_smul, Real.norm_of_nonneg (by linarith [ht.1])]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt hv
  have hη : g.IsGeodesicOn η (Icc (1 : ℝ) 2) := by
    intro t ht
    apply hgw.comp_affine (-1) 2
    simp only [mem_preimage, mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
    rw [norm_smul, Real.norm_of_nonneg (by linarith [ht.2])]
    exact (mul_le_mul_of_nonneg_right (by linarith [ht.1] : -1 * t + 2 ≤ 1)
      (norm_nonneg w)).trans_lt (by simpa using hw)
  have hdev := hasFDerivAt_endpoint_chart
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hvmem)).mdifferentiableAt (by simp))
  have hdew := hasFDerivAt_endpoint_chart
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hwmem)).mdifferentiableAt (by simp))
  have hγd : HasDerivAt (fun t => extChartAt (𝓡 n) (e v) (γ t))
      (mfderiv (𝓡 n) (𝓡 n) e v v) 1 := by
    have hdev' : HasFDerivAt (fun x => extChartAt (𝓡 n) (e v) (e x))
        (show EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) from
          mfderiv (𝓡 n) (𝓡 n) e v) ((1 : ℝ) • v) := by
      simpa only [one_smul] using hdev
    simpa only [γ, one_smul, Function.comp_def] using!
      hdev'.comp_hasDerivAt 1 ((hasDerivAt_id (1 : ℝ)).smul_const v)
  have hηd : HasDerivAt (fun t => extChartAt (𝓡 n) (e v) (η t))
      (-mfderiv (𝓡 n) (𝓡 n) e w w) 1 := by
    rw [heq]
    have hs : HasDerivAt (fun t : ℝ => (-1 * t + 2) • w) (-w) 1 := by
      simpa using (((hasDerivAt_id (1 : ℝ)).const_mul (-1)).add_const 2).smul_const w
    have hdew' : HasFDerivAt (fun x => extChartAt (𝓡 n) (e w) (e x))
        (show EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) from
          mfderiv (𝓡 n) (𝓡 n) e w) ((-(1 : ℝ) * 1 + 2) • w) := by
      norm_num
      exact hdew
    simpa only [η, Function.comp_def, map_neg] using! hdew'.comp_hasDerivAt 1 hs
  have hpos : γ 1 = η 1 := by norm_num [γ, η]; exact heq
  have hgerm := hγ.eq_nhds_of_initial_data hη (by norm_num : (1 : ℝ) ∈ Icc 1 2)
    (e v) (by simp [γ]) hpos
    (hγd.deriv.trans (hvel.trans hηd.deriv.symm))
  have h := hγ.eqOn_of_eq_nhds hη (convex_Icc _ _).isPreconnected
    (by norm_num : (1 : ℝ) ∈ Icc 1 2) hgerm (by norm_num : (2 : ℝ) ∈ Icc 1 2)
  simpa [γ, η] using h

end PoincareConjecture.RiemannianMetric
