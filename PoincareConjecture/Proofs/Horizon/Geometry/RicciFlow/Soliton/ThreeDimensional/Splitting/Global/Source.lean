import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Soliton
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Homothety
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.SourceNoncollapse








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem hessian_eq_of_metric_eq {g h : RiemannianMetric n M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h)
    (f : M → ℝ) (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.hessian f x v w = D'.hessian f x v w := by
  subst h
  unfold LeviCivitaData.hessian LeviCivitaData.hessianOnFields
  rw [D.connection_eq_of_mdifferentiableAt D'
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) w)]

private theorem ricci_eq_of_metric_eq {g h : RiemannianMetric n M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.ricci x v w = D'.ricci x v w := by
  subst h
  simp only [LeviCivitaData.ricci, D.horizon_curvatureTensor_eq D']

private theorem curvatureTensor_eq_of_metric_eq {g h : RiemannianMetric n M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h)
    (x : M) (v w a b : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x v w a b = D'.curvatureTensor x v w a b := by
  subst h
  exact D.horizon_curvatureTensor_eq D' x v w a b

private theorem ricciNullity_eq_of_metric_eq {g h : RiemannianMetric n M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h) (x : M) :
    ricciNullity D x = ricciNullity D' x := by
  unfold ricciNullity
  have hker : ricciKernel D x = ricciKernel D' x := by
    apply Submodule.ext
    intro v
    simp only [mem_ricciKernel, ricci_eq_of_metric_eq D D' heq]
  rw [hker]

end PoincareConjecture.RicciFlow.Splitting

namespace PoincareConjecture.ShrinkingSolitonFlow

open RicciFlow.Splitting

variable {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)

theorem ancientSourceFlow_soliton_equation (x : M) (v w : TangentSpace (𝓡 3) x) :
    (G.ancientSourceFlow.connection 0).ricci x v w +
      (G.ancientSourceFlow.connection 0).hessian S.potential x v w =
        (1 / 2 : ℝ) * (G.ancientSourceFlow.metric 0).inner x v w := by
  rw [ricci_eq_of_metric_eq _ S.connection G.ancientSourceFlow_metric_zero,
    hessian_eq_of_metric_eq _ S.connection G.ancientSourceFlow_metric_zero,
    G.ancientSourceFlow_metric_zero]
  exact S.soliton_equation x v w

theorem ricciNullity_eq_one_of_null_plane
    (hC : RicciFlowCurvatureTheory.{u})
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : S.metric.inner x v v = 1) (hw : S.metric.inner x w w = 1)
    (hvw : S.metric.inner x v w = 0)
    (hzero : S.connection.curvatureTensor x v w v w = 0) :
    ∀ t < 0, ∀ y, ricciNullity (G.flow.connection t) y = 1 := by
  have hmetric := G.ancientSourceFlow_metric_zero
  have hdim := G.ancientSourceFlow.ricciNullity_eq_one_of_terminal_null_plane hC
    G.ancientSource.nonnegative_curvature_operator (G.ancientSource.nonflat 0 le_rfl)
    x v w (by simpa only [hmetric] using hv) (by simpa only [hmetric] using hw)
    (by simpa only [hmetric] using hvw) (by
      rw [curvatureTensor_eq_of_metric_eq _ S.connection hmetric]
      exact hzero)
  have hS (y : M) : ricciNullity S.connection y = 1 := by
    rw [← ricciNullity_eq_of_metric_eq _ S.connection hmetric]
    exact hdim y
  intro t ht y
  obtain ⟨E⟩ := G.self_similar t ht
  rw [E.ricciNullity (abs_pos.mpr ht.ne) S.connection (G.flow.connection t)]
  exact hS _

theorem exists_complete_nullCover_coordinate
    (hC : RicciFlowCurvatureTheory.{u})
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : S.metric.inner x v v = 1) (hw : S.metric.inner x w w = 1)
    (hvw : S.metric.inner x v w = 0)
    (hzero : S.connection.curvatureTensor x v w v w = 0) :
    ∃ hc : IsCoveringMap (unitRicciKernelProjection (G.ancientSourceFlow.connection 0)),
      (∀ y : M, Nat.card (unitRicciKernelProjection
        (G.ancientSourceFlow.connection 0) ⁻¹' {y}) = 2) ∧
      letI := unitRicciKernelChartedSpace (G.ancientSourceFlow.connection 0) hc
      letI := unitRicciKernelIsManifold (G.ancientSourceFlow.connection 0) hc
      letI := unitRicciKernelT3Space (G.ancientSourceFlow.connection 0) hc
      let g' := unitRicciKernelMetric (G.ancientSourceFlow.connection 0) hc
      let r := unitRicciKernelCoordinate (G.ancientSourceFlow.connection 0) S.potential
      MetricComplete g' ∧ ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r ∧
        RiemannianMetric.HasUnitGradient g'.leviCivitaData r ∧
        RiemannianMetric.HasZeroHessian g'.leviCivitaData r ∧
        ∀ p, r (unitRicciKernelReverse (G.ancientSourceFlow.connection 0) p) = -r p := by
  apply RicciFlow.Splitting.exists_complete_nullCover_coordinate hC G.ancientSourceFlow
    G.ancientSource.nonnegative_curvature_operator (G.ancientSource.nonflat 0 le_rfl)
    (G.ancientSource.complete 0 le_rfl) S.potential S.potential_C2
    G.ancientSourceFlow_soliton_equation x v w
  · simpa only [G.ancientSourceFlow_metric_zero] using hv
  · simpa only [G.ancientSourceFlow_metric_zero] using hw
  · simpa only [G.ancientSourceFlow_metric_zero] using hvw
  · rw [curvatureTensor_eq_of_metric_eq _ S.connection G.ancientSourceFlow_metric_zero]
    exact hzero

end PoincareConjecture.ShrinkingSolitonFlow
