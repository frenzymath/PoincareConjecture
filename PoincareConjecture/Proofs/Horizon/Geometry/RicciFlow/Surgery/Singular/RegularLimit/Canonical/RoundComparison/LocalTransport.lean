import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComparison.ScalarModulus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorNaturality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.SingularRegularLimit.RoundComparison

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem tensorNorm_iteratedCovariantDerivative_pullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {k : ℕ} {S : CovariantTensorEvaluation n M k} {T : CovariantTensorEvaluation n N k}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (hST : ∀ y ∈ U, ∀ v,
      S y v = T (f y) (fun i => mfderiv (𝓡 n) (𝓡 n) f y (v i)))
    (m : ℕ) {x : M} (hx : x ∈ U) :
    g.tensorNorm (D.iteratedCovariantTensorDerivative S m) x =
      h.tensorNorm (D'.iteratedCovariantTensorDerivative T m) (f x) := by
  obtain ⟨e, he⟩ := hinv x hx
  obtain ⟨A, hA⟩ := (D'.iteratedCovariantTensorDerivative_isSmooth hT m).1 (f x)
  apply g.tensorNorm_eq_of_linearEquiv h _ _ x (f x) e.toLinearEquiv
      (fun u v => ?_) (fun v => ?_) A hA
  · change h.inner (f x) (e u) (e v) = g.inner x u v
    have heval (v : TangentSpace (𝓡 n) x) : e v = mfderiv (𝓡 n) (𝓡 n) f x v :=
      congrArg (fun L => L v) he
    simpa only [heval] using (hmetric x hx u v).symm
  · have heval (v : TangentSpace (𝓡 n) x) : e v = mfderiv (𝓡 n) (𝓡 n) f x v :=
      congrArg (fun L => L v) he
    simpa only [ContinuousLinearEquiv.coe_toLinearEquiv, heval] using
      D.iteratedCovariantTensorDerivative_eq_pullback D' hU hf hinv hmetric hS hT hST m hx v

def scalarTolerance
    {g₀ : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D₀ : LeviCivitaData g₀) (p : EuclideanSpace ℝ (Fin n))
    {α : ℝ} (hα : 0 < α) : ℝ :=
  (exists_scalar_control_of_covariant_metric_twoJet D₀ p hα).choose

theorem scalarTolerance_pos
    {g₀ : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D₀ : LeviCivitaData g₀) (p : EuclideanSpace ℝ (Fin n))
    {α : ℝ} (hα : 0 < α) : 0 < scalarTolerance D₀ p hα :=
  (exists_scalar_control_of_covariant_metric_twoJet D₀ p hα).choose_spec.1

theorem scalar_control_of_local_isometry
    {g₀ : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D₀ : LeviCivitaData g₀) (p : EuclideanSpace ℝ (Fin n))
    {α : ℝ} (hα : 0 < α)
    {gM hM : RiemannianMetric n M} (DM : LeviCivitaData gM) (DH : LeviCivitaData hM)
    {f : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hp : p ∈ U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ v w : EuclideanSpace ℝ (Fin n),
      g₀.inner y v w = gM.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v)
        (mfderiv (𝓡 n) (𝓡 n) f y w))
    (hclose : ∀ r : ℕ, r ≤ 2 → gM.tensorNorm
      (DM.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → TangentSpace (𝓡 n) y) =>
          hM.inner y (v 0) (v 1) - gM.inner y (v 0) (v 1)) r)
      (f p) < scalarTolerance D₀ p hα) :
    |DH.scalarCurvature (f p) - D₀.scalarCurvature p| < α := by
  have hB : ContDiffOn ℝ ∞ (hM.pullbackCoefficients f) U := by
    intro y hy
    exact (hM.contDiffAt_pullbackCoefficients
      (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  have hpos (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U)
      (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
      0 < hM.pullbackCoefficients f y v v := by
    obtain ⟨e, he⟩ := hinv y hy
    apply hM.pos
    intro hz
    apply hv
    apply e.injective
    calc
      e v = mfderiv (𝓡 n) (𝓡 n) f y v := congrArg (fun L => L v) he
      _ = 0 := hz
      _ = e 0 := (map_zero e).symm
  obtain ⟨hE, V, hV, hpV, hVU, hEeq⟩ := RiemannianMetric.exists_local_extension
    hU hp (hM.pullbackCoefficients f) hB
    (fun y _ v w => hM.symm (f y) _ _) hpos
  let DE := hE.euclideanLeviCivitaData
  have hEmetric (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V)
      (v w : EuclideanSpace ℝ (Fin n)) :
      hE.inner y v w = hM.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v)
        (mfderiv (𝓡 n) (𝓡 n) f y w) := by
    change hE.euclideanCoefficients y v w = hM.pullbackCoefficients f y v w
    rw [hEeq y hy]
  have hjet (r : ℕ) :
      g₀.tensorNorm (D₀.iteratedCovariantTensorDerivative
        (metricDifferenceTensor g₀ hE) r) p =
      gM.tensorNorm (DM.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → TangentSpace (𝓡 n) y) =>
          hM.inner y (v 0) (v 1) - gM.inner y (v 0) (v 1)) r) (f p) := by
    apply tensorNorm_iteratedCovariantDerivative_pullback D₀ DM hV (hf.mono hVU)
      (fun y hy => hinv y (hVU hy)) (fun y hy => hmetric y (hVU hy))
      (metricDifferenceTensor_isSmooth g₀ hE)
      ((Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor hM).sub
        (Poincare.RicciFlow.Harnack.metric_isSmoothCovariantTensor gM))
      (fun y hy v => ?_) r hpV
    exact congrArg₂ (· - ·) (hEmetric y hy (v 0) (v 1))
      (hmetric y (hVU hy) (v 0) (v 1))
  have hscalar := (exists_scalar_control_of_covariant_metric_twoJet D₀ p hα).choose_spec.2
    hE DE (fun r hr => (hjet r).trans_lt (hclose r hr))
  have htransport := DE.scalarCurvature_eq_of_local_isometry DH hV
    (hf.mono hVU) hEmetric hpV
  rwa [htransport] at hscalar

end PoincareConjecture.SingularRegularLimit.RoundComparison
