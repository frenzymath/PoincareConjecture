import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.HarmonicKernel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.GrowingRegularity.TimeDerivatives
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.Principal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric.UniformHarmonicLift

open LeviCivitaData Poincare.Parabolic.Interior

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)

omit [NeZero n] [T3Space M] [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M] in
theorem principalOperator_elliptic_bounds
    {O : M} {r C A : ℝ} (F : UniformHarmonicLift g O r C A) (hC : 0 < C)
    {x : E} (hx : x ∈ Metric.ball 0 (2 * r)) (v : E) :
    (1 / C) * ‖v‖ ^ 2 ≤ inner ℝ v (F.h.principalOperator x v) ∧
      inner ℝ v (F.h.principalOperator x v) ≤ C * ‖v‖ ^ 2 := by
  simpa only [one_div, inv_inv] using
    F.h.principalOperator_elliptic x (inv_pos.mpr hC) hC
      (fun v => (F.helliptic x hx v).1) (fun v => (F.helliptic x hx v).2) v

omit [NeZero n] [T3Space M] [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M] in
theorem principalOperator_holder_bound
    {O : M} {r C A : ℝ} (F : UniformHarmonicLift g O r C A)
    (hC : 0 < C) (hA : 0 ≤ A)
    {x y : E} (hx : x ∈ Metric.ball 0 (2 * r)) (hy : y ∈ Metric.ball 0 (2 * r)) :
    ‖F.h.principalOperator x - F.h.principalOperator y‖ ≤
      (A * Real.sqrt (2 * (2 * r)) / (C⁻¹) ^ 2) * ‖x - y‖ ^ (1 / 2 : ℝ) :=
  F.h.norm_principalOperator_sub_le_rpow (inv_pos.mpr hC) hA
    (fun z hz v => (F.helliptic z hz v).1) F.hderiv hx hy

theorem timeDerivative_exhaustionKernel_pullback
    {O : M} {r C A : ℝ} (F : UniformHarmonicLift g O r C A)
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (y : M) {x : E} (hx : x ∈ Metric.ball 0 (2 * r)) {t : ℝ} (ht : 0 < t) :
    let f := fun p : E × ℝ => dirichletExhaustionKernel
      (fun q => Dirichlet.heatKernelContinuousTime D (S q)) p.2 (F.e p.1) y
    timeDerivative f (x, t) = Kernel.matrixLap (coefficientMatrix (F.h.principalOperator x))
      (spatialDerivative (spatialDerivative f) (x, t)) := by
  intro f
  have hf : ContDiffOn ℝ ∞ f (Metric.ball 0 (2 * r) ×ˢ Ioi 0) :=
    F.contDiffOn_exhaustionKernel_pullback D hc hk hRic S hΩmono hcover y
  have hU : IsOpen (Metric.ball (0 : E) (2 * r) ×ˢ Ioi (0 : ℝ)) :=
    Metric.isOpen_ball.prod isOpen_Ioi
  have hp : (x, t) ∈ Metric.ball 0 (2 * r) ×ˢ Ioi 0 := ⟨hx, ht⟩
  have hfd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hdt : HasDerivAt (fun s => f (x, s)) (timeDerivative f (x, t)) t :=
    hfd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  obtain ⟨f', hf', _, heq⟩ := exists_compact_smooth_extension
    (isCompact_singleton (x := (x, t))) hU (singleton_subset_iff.mpr hp) hf
  have heq' := heq (x, t) (by simp)
  have hess := fderiv_fderiv_spatialSlice_eq_of_eventuallyEq heq'
  rw [fderiv_fderiv_spatialSlice hf',
    spatialDerivative_spatialDerivative_eq_of_eventuallyEq heq'] at hess
  have hheat := F.hasDerivAt_exhaustionKernel_pullback D hc hk hRic S hΩmono hcover y hx ht
  have he := hdt.unique hheat
  rw [matrixLap_coefficientMatrix]
  simp only [F.h.inner_basis_principalOperator_basis, smul_eq_mul]
  rw [hess]
  exact he

end PoincareConjecture.RiemannianMetric.UniformHarmonicLift
