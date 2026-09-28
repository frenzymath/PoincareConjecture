import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.RescaledEstimate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.Principal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData




theorem exists_uniform_harmonic_heat_second_derivative_bound
    (n : ℕ) (hn : 1 ≤ n) {r a b G : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) (hG : 0 ≤ G) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 (r * 2), ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.inner x v v ∧ g.inner x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 (r * 2), ‖fderiv ℝ g.euclideanCoefficients x‖ ≤ G) →
        (∀ x ∈ Metric.ball 0 (r * 2), ∀ i : Fin n,
          D.laplacian (fun y : EuclideanSpace ℝ (Fin n) ↦ y i) x = 0) →
        ∀ B : ℝ, 0 ≤ B → ∀ f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ,
          ContDiffOn ℝ ∞ f (Metric.ball 0 (r * 2) ×ˢ Ioo 0 2) →
          (∀ x ∈ Metric.ball 0 (r * 2), ∀ t ∈ Ioc (0 : ℝ) 1,
            HasDerivAt (fun s ↦ f (x, s)) (D.laplacian (fun y ↦ f (y, t)) x) t) →
          (∀ x ∈ Metric.ball 0 (r * 2), ∀ t ∈ Ioc (0 : ℝ) 1, |f (x, t)| ≤ B) →
          ‖fderiv ℝ (fderiv ℝ (fun y ↦ f (y, 1))) 0‖ ≤ C * B := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨C, hC, hestimate⟩ :=
    Poincare.Parabolic.exists_uniform_interior_heat_hessian_bound_scaled n hn
      (lam := 1 / b) (Λ := 1 / a) (H := (G * Real.sqrt (2 * (r * 2))) / a ^ 2)
      hr (by positivity) (one_div_le_one_div_of_le ha hab) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro g D hell hderiv hharm B hB f hf hheat hvalue
  apply hestimate g.principalOperator g.contDiff_principalOperator.contDiffOn
    (fun x _ ↦ g.principalOperator_symmetric x)
    (fun x hx ↦ g.principalOperator_elliptic x ha hb
      (fun v ↦ (hell x hx v).1) (fun v ↦ (hell x hx v).2))
    (fun x hx y hy ↦ g.norm_principalOperator_sub_le_rpow ha hG
      (fun z hz v ↦ (hell z hz v).1) hderiv hx hy) B hB f hf ?_ hvalue
  intro x hx t ht
  have hslice : ContDiffAt ℝ ∞ (fun y ↦ f (y, t)) x := by
    have hxt : (x, t) ∈ Metric.ball 0 (r * 2) ×ˢ Ioo (0 : ℝ) 2 :=
      ⟨hx, ht.1, lt_of_le_of_lt ht.2 (by norm_num)⟩
    exact (hf.contDiffAt ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hxt)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  have h := hheat x hx t ht
  rw [D.laplacian_eq_sum_fderiv_of_harmonic hslice (hharm x hx)] at h
  simpa only [g.inner_basis_principalOperator_basis] using h

end PoincareConjecture.LeviCivitaData
