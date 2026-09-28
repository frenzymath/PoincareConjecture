import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundComponent
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundComponentJets
import PoincareConjecture.Proofs.M13.CurvatureContractions
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Equation
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology Uniformity

universe u

namespace PoincareConjecture.M28.tube

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

open PoincareConjecture.SpacetimeBounds

noncomputable def roundMetricJetNorm
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (j : ℕ)
    (x : N.model.carrier) : ℝ :=
  N.model_metric.tensorNorm
    (N.model_connection.iteratedCovariantTensorDerivative
      (fun y v => N.scale * singularMetricPullback g N.forward y v -
        N.model_metric.inner y (v 0) (v 1)) j) x

theorem roundMetricJetNorm_lt
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    (horder : 2 ≤ ⌊epsilon⁻¹⌋₊)
    (x : N.model.carrier) (j : ℕ) (hj : j ≤ 2) :
    roundMetricJetNorm N j x < epsilon := by
  obtain ⟨bound, hbound, hmetric⟩ := N.metric_comparison
  simpa [roundMetricJetNorm] using
    (singularMetricJetNorm_lt_of_error_lt N.model_metric N.model_connection
      (fun y v => N.scale * singularMetricPullback g N.forward y v)
      ⌊epsilon⁻¹⌋₊ j x (hj.trans horder) N.epsilon_pos (hmetric x) hbound)

noncomputable def jetScalarCurvature (J : MetricTwoJet 3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    EuclideanSpace.proj j (J.1.inverse (EuclideanSpace.proj i)) *
      jetRicci J (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j)

theorem contDiffAt_jetScalarCurvature
    {J : MetricTwoJet 3} (hJ : J.1.IsInvertible) :
    ContDiffAt ℝ ∞ jetScalarCurvature J := by
  unfold jetScalarCurvature
  have hI : ContDiffAt ℝ ∞
      (fun K : MetricTwoJet 3 => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hentry : ContDiffAt ℝ ∞
      (fun K : MetricTwoJet 3 =>
        EuclideanSpace.proj j (K.1.inverse (EuclideanSpace.proj i))) J := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp J
      (hI.clm_apply contDiffAt_const)
  exact hentry.mul (contDiffAt_jetRicci hJ
    (EuclideanSpace.basisFun (Fin 3) ℝ i)
    (EuclideanSpace.basisFun (Fin 3) ℝ j))

theorem exists_jetScalarCurvature_modulus
    {J : MetricTwoJet 3} (hJ : J.1.IsInvertible)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ K : MetricTwoJet 3, dist K J < eta →
        |jetScalarCurvature K - jetScalarCurvature J| < delta := by
  have hcont : ContinuousAt jetScalarCurvature J :=
    (contDiffAt_jetScalarCurvature hJ).continuousAt
  obtain ⟨eta, heta, hK⟩ := (Metric.continuousAt_iff.mp hcont) delta hdelta
  refine ⟨eta, heta, ?_⟩
  intro K hdist
  have hdist' := hK hdist
  simpa [Real.dist_eq] using hdist'

theorem exists_jetScalarCurvature_uniform_modulus
    {K : Set (MetricTwoJet 3)} (hK : IsCompact K)
    (hInvertible : ∀ J ∈ K, J.1.IsInvertible)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ J ∈ K, ∀ L : MetricTwoJet 3, dist L J < eta →
        |jetScalarCurvature L - jetScalarCurvature J| < delta := by
  have hcontinuous : ∀ J ∈ K, ContinuousAt jetScalarCurvature J := by
    intro J hJ
    exact (contDiffAt_jetScalarCurvature (hInvertible J hJ)).continuousAt
  have huniform :
      {p : MetricTwoJet 3 × MetricTwoJet 3 |
        p.1 ∈ K → dist (jetScalarCurvature p.1)
          (jetScalarCurvature p.2) < delta} ∈
        𝓤 (MetricTwoJet 3) := by
    exact hK.uniformContinuousAt_of_continuousAt jetScalarCurvature
      hcontinuous (Metric.dist_mem_uniformity hdelta)
  obtain ⟨eta, heta, hnear⟩ := Metric.mem_uniformity_dist.mp huniform
  refine ⟨eta, heta, ?_⟩
  intro J hJ L hLJ
  have hp : ((J, L) : MetricTwoJet 3 × MetricTwoJet 3) ∈
      {p : MetricTwoJet 3 × MetricTwoJet 3 |
        p.1 ∈ K → dist (jetScalarCurvature p.1)
          (jetScalarCurvature p.2) < delta} := by
    exact hnear (by simpa [dist_comm] using hLJ)
  simpa [Real.dist_eq, abs_sub_comm] using hp hJ

theorem round_scalar_ratio_of_normalized_close
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    (D : LeviCivitaData g)
    {delta : ℝ} (_hdelta : 0 < delta) (hdelta_one : delta < 1)
    (hclose : ∀ x ∈ N.carrier,
      |D.scalarCurvature x / N.scale - 6| < delta) :
    ∀ x ∈ N.carrier,
      ∀ y ∈ N.carrier, D.scalarCurvature x ≤ 2 * D.scalarCurvature y := by
  intro x hx y hy
  have hxclose := abs_lt.mp (hclose x hx)
  have hyclose := abs_lt.mp (hclose y hy)
  have hscale : 0 < N.scale := N.scale_pos
  have hxupper : D.scalarCurvature x / N.scale < 7 := by
    linarith
  have hylower : 5 < D.scalarCurvature y / N.scale := by
    linarith
  have hxupper' : D.scalarCurvature x < 7 * N.scale := by
    exact (div_lt_iff₀ hscale).mp hxupper
  have hylower' : 5 * N.scale < D.scalarCurvature y := by
    exact (lt_div_iff₀ hscale).mp hylower
  linarith

theorem jetRicci_metricTwoJet_eq
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (D : LeviCivitaData g) (x u v : EuclideanSpace ℝ (Fin 3)) :
    jetRicci (metricTwoJet g.euclideanCoefficients x) u v = D.ricci x u v := by
  exact jetRicci_metricTwoJet D x u v

theorem LeviCivitaData.scalarCurvature_eq_inverse_gram_m28
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold (𝓡 n) ∞ X] [T2Space X]
    {g : RiemannianMetric n X} (D : LeviCivitaData g) (x : X)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    D.scalarCurvature x = ∑ i, ∑ j,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j *
        D.ricci x (b i) (b j) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact bilinear_sum_basis_eq_inverse_gram (M13.ricciLinear D x) b
    (g.orthonormalBasis x)

theorem RiemannianMetric.inverseCoefficients_eq_inverse_gram_m28 {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    g.inverseCoefficients x i j =
      (Matrix.of (fun a b => g.inner x
        (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)))⁻¹ i j := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := congrArg (fun v : TangentSpace (𝓡 n) x =>
      EuclideanSpace.proj j v)
    ((g.orthonormalBasis x).sum_repr'
      ((g.inner x).inverse (EuclideanSpace.proj i)))
  have hp (k : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      inner ℝ (g.orthonormalBasis x k)
          ((g.inner x).inverse (EuclideanSpace.proj i)) =
        EuclideanSpace.proj i (g.orthonormalBasis x k) := by
    change g.inner x (g.orthonormalBasis x k)
      ((g.inner x).inverse (EuclideanSpace.proj i)) = _
    rw [g.symm, (g.inner_isInvertible x).self_apply_inverse]
    rfl
  have hexp : g.inverseCoefficients x i j =
      ∑ k, EuclideanSpace.proj i (g.orthonormalBasis x k) *
        EuclideanSpace.proj j (g.orthonormalBasis x k) := by
    simpa only [OrthonormalBasis.repr_apply_apply, hp, map_sum, map_smul,
      smul_eq_mul, RiemannianMetric.inverseCoefficients] using h.symm
  rw [hexp]
  convert! sum_basis_repr_mul_eq_inverse_gram
      (show Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x) from
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
      (g.orthonormalBasis x) i j using 1

theorem jetScalarCurvature_metricTwoJet_eq
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin 3)) :
    jetScalarCurvature (metricTwoJet g.euclideanCoefficients x) =
      D.scalarCurvature x := by
  rw [LeviCivitaData.scalarCurvature_eq_inverse_gram_m28 D x
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  simp only [jetScalarCurvature, jetRicci_metricTwoJet D]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact RiemannianMetric.inverseCoefficients_eq_inverse_gram_m28 g x i j

theorem jetScalarCurvature_metricTwoJet_pullback
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin 3) → M}
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U)
    (hi : ∀ y ∈ U,
      (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U) :
    jetScalarCurvature (metricTwoJet (g.pullbackCoefficients e) x) =
      D.scalarCurvature (e x) := by
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) U := fun y hy =>
    (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨gE, DE, V, hV, hxV, hVU, heq⟩ :=
    RiemannianMetric.exists_local_realization hU hx
      (g.pullbackCoefficients e) hcoeff
      (fun y _ u v => g.symm (e y) _ _)
      (fun y hy w hw => by
        apply g.pos (e y)
        intro hz
        apply hw
        apply (hi y hy).injective
        rw [map_zero]
        convert! hz using 1)
  have hmetric (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ V)
      (u v : EuclideanSpace ℝ (Fin 3)) :
      gE.inner y u v = g.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y u)
        (mfderiv (𝓡 3) (𝓡 3) e y v) :=
    congrArg (fun B => B u v) (heq y hy)
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 x]
      g.pullbackCoefficients e := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  rw [← SpacetimeBounds.metricTwoJet_congr_of_eventuallyEq hB,
    jetScalarCurvature_metricTwoJet_eq DE]
  exact DE.scalarCurvature_eq_of_local_isometry D hV (he.mono hVU)
    hmetric hxV

end PoincareConjecture.M28.tube
