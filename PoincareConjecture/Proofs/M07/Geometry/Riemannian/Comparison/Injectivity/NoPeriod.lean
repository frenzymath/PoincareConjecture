import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.FiniteOrbit
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PullbackGeodesics
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.OrbitConvexity














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem false_of_short_finite_period
    {n : ℕ} (G : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (D : LeviCivitaData G)
    (hgauss : ∀ x w : EuclideanSpace ℝ (Fin n), G.inner x x w = inner ℝ x w)
    (hnorm : ∀ a b : EuclideanSpace ℝ (Fin n), G.inner 0 a b = inner ℝ a b)
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ G.tangentNorm x v ∧ G.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    {m : ℕ} (hm : 0 < m) {r δ K : ℝ} (hr : 0 < r)
    (hδ : δ < r / 16) (henergy : (m : ℝ) * δ ^ 2 < (r / 16) ^ 2)
    (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hdom : Metric.closedBall 0 r ⊆ U)
    (hsmooth : ∀ i : Fin m, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (d^[i.val]) U)
    (hcenter : ∀ i : Fin m, ‖d^[i.val] 0‖ ≤ δ)
    (hperiod : EqOn (d^[m]) id (Metric.closedBall 0 r))
    (hdisplace : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r,
      ‖d x‖ ≤ δ + 2 * ‖x‖)
    (hfree : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r, d x ≠ x)
    (hmetric : ∀ i : Fin m, ∀ x ∈ Metric.ball 0 r,
      ∀ a b : EuclideanSpace ℝ (Fin n), G.inner x a b = G.inner (d^[i.val] x)
        (mfderiv (𝓡 n) (𝓡 n) (d^[i.val]) x a)
        (mfderiv (𝓡 n) (𝓡 n) (d^[i.val]) x b))
    (hsmall : ∀ i : Fin m, ∀ x ∈ Metric.ball 0 r,
      ‖d^[i.val] x‖ ≤ Poincare.ODE.Jacobi.comparisonRadius K / 4)
    (hcurv : ∀ i : Fin m, ∀ x ∈ Metric.ball 0 r, ∀ t ∈ Icc (0 : ℝ) 1,
      D.curvatureTensorNorm (t • d^[i.val] x) ≤ K) : False := by
  have hcont : ∀ i : Fin m, ContinuousOn (d^[i.val]) (Metric.closedBall 0 r) :=
    fun i x hx => ((hsmooth i).contMDiffAt
      (hU.mem_nhds (hdom hx))).continuousAt.continuousWithinAt
  have hsmooth' : ∀ i : Fin m,
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ (d^[i.val]) (Metric.ball 0 r) :=
    fun i => (hsmooth i).mono (Metric.ball_subset_closedBall.trans hdom)
  obtain ⟨y, hne, hy, hdy, hminy, hminDy⟩ :=
    exists_two_finite_orbit_energy_minimizers hm hr hδ henergy d hcont hcenter
      hperiod hdisplace hfree
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, _, hconfine⟩ :=
    G.exists_confined_minimizing_geodesic_of_uniform_tangentNorm_bounds hbound y (d y)
  have hends : ‖d y - y‖ < r / 4 := by
    have h := norm_sub_le (d y) y
    linarith
  have hγball (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, dist_zero_right]
    have h := hconfine t ht
    linarith
  let I := Ioo (-ε) (1 + ε) ∩ γ ⁻¹' Metric.ball 0 r
  have hI : IsOpen I :=
    hγ.contMDiffOn.continuousOn.isOpen_inter_preimage isOpen_Ioo Metric.isOpen_ball
  have hsub : Icc (0 : ℝ) 1 ⊆ I := by
    intro t ht
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hγball t ht⟩
  have hγI : G.IsGeodesicOn γ I := fun t ht => hγ t ht.1
  have hgeo (i : Fin m) : G.IsGeodesicOn ((d^[i.val]) ∘ γ) I :=
    hγI.comp_local_isometry Metric.isOpen_ball (hsmooth' i) (hmetric i) hI
      (fun _ ht => ht.2)
  have hstrict : StrictConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun t => ∑ i : Fin m, ‖d^[i.val] (γ t)‖ ^ 2) := by
    apply RiemannianMetric.strictConvexOn_sum_norm_sq_of_geodesics D hgauss hnorm
      Finset.univ (fun i : Fin m => (d^[i.val]) ∘ γ)
      (fun i _ => hgeo i) hI zero_le_one hsub
      (j := ⟨0, hm⟩) (Finset.mem_univ _) ?_
      (fun i _ t ht => hsmall i (γ t) (hγball t ht))
      (fun i _ t ht s hs => hcurv i (γ t) (hγball t ht) s hs)
    simpa only [Function.comp_apply, Function.iterate_zero, id_eq, hγ0, hγ1] using hne
  have heq := eq_of_strictConvexOn_curve_of_isMinOn hminy hminDy γ
    (fun t ht => Metric.ball_subset_closedBall (hγball t ht)) hγ0 hγ1
    (fun _ => hstrict)
  exact hne heq

end PoincareConjecture
