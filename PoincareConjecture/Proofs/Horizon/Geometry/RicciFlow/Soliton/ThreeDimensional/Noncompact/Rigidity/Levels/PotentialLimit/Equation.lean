import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.TimeDerivative

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem hessian_in_smooth_parametrization (D : LeviCivitaData g)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    {f : M → ℝ} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e x))
    (v w : EuclideanSpace ℝ (Fin n)) :
    D.hessian f (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) =
      fderiv ℝ (fderiv ℝ (f ∘ e)) x v w - fderiv ℝ (f ∘ e) x
        (CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) x v w) := by
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) U := by
    intro y hy
    exact (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨gE, DE, V, hVo, hxV, _, hE⟩ :=
    RiemannianMetric.exists_local_realization hU hx
      (g.pullbackCoefficients e) hcoeff (fun y _ a b => g.symm _ _ _)
      (fun y hy a ha => by
        apply g.pos (e y)
        intro hzero
        apply ha
        apply (hi y hy).injective
        rw [map_zero]
        exact hzero)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e := by
    filter_upwards [hVo.mem_nhds hxV] with y hy
    exact hE y hy
  have hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible :=
    Filter.mem_of_superset (hU.mem_nhds hx) hi
  have hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : EuclideanSpace ℝ (Fin n),
      gE.inner y a b = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y a) (mfderiv (𝓡 n) (𝓡 n) e y b) := by
    filter_upwards [heq] with y hy a b
    exact congrArg (fun C => C a b) hy
  have hΓ : CoordinateExponential.christoffelBilinear gE.euclideanCoefficients x =
      CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) x := by
    simp only [CoordinateExponential.christoffelBilinear, heq.self_of_nhds, heq.fderiv_eq]
  rw [← DE.hessian_comp_of_metric_pullback D
    (he.contMDiffAt (hU.mem_nhds hx)) hinv hmetric hf,
    DE.hessian_eq_fderiv_sub_christoffel
      (contMDiffAt_iff_contDiffAt.mp (hf.comp x (he.contMDiffAt (hU.mem_nhds hx)))), hΓ]

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.ShrinkingSolitonFlow

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] in
private theorem ricci_eq_of_metric_eq {g h : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h)
    (x : M) (v w : TangentSpace (𝓡 3) x) : D.ricci x v w = D'.ricci x v w := by
  subst h
  simp only [LeviCivitaData.ricci, D.horizon_curvatureTensor_eq D']

theorem normalizedPotential_fderiv2_in_parametrization (q : M)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin 3) → M}
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fderiv ℝ (S.normalizedPotential q ∘ e)) x v w =
      fderiv ℝ (S.normalizedPotential q ∘ e) x
        (CoordinateExponential.christoffelBilinear
          (fun y => (G.unscaledSourceFlow.metric 0).pullbackCoefficients e y) x v w) +
      ((G.unscaledSourceFlow.metric 0).pullbackCoefficients e x v w +
        deriv (fun t => (G.unscaledSourceFlow.metric t).pullbackCoefficients e x) 0 v w) /
          (2 * S.potentialGradientScale q) := by
  have hHess := S.connection.hessian_in_smooth_parametrization hU he hi hx
    (S.normalizedPotential_contMDiff q _) v w
  rw [S.hessian_normalizedPotential] at hHess
  have hflow := G.unscaledSourceFlow.deriv_pullbackCoefficients_apply
    isOpen_Iio hU he (by norm_num : (0 : ℝ) ∈ Iio 1) hx v w
  rw [ricci_eq_of_metric_eq (G.unscaledSourceFlow.connection 0) S.connection
    G.unscaledSourceFlow_metric_zero] at hflow
  have hsol := S.soliton_equation (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w)
  rw [G.unscaledSourceFlow_metric_zero]
  rw [hflow]
  have hess : S.connection.hessian S.potential (e x)
      (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) =
        (1 / 2 : ℝ) * S.metric.pullbackCoefficients e x v w -
          S.connection.ricci (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
            (mfderiv (𝓡 3) (𝓡 3) e x w) := by
    change _ = (1 / 2 : ℝ) * S.metric.inner _ _ _ - _
    exact eq_sub_of_add_eq' hsol
  rw [hess] at hHess
  simp only [div_eq_mul_inv, mul_inv_rev] at *
  norm_num only [invOf_eq_inv, inv_inv, one_div, inv_pos] at *
  linear_combination -hHess

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

theorem normalizedPotentialPullback_fderiv2
    (z : L.limitCarrier.carrier) (k : ℕ) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (extChartAt (𝓡 3) z).target)
    (hxk : (extChartAt (𝓡 3) z).symm x ∈ L.exhaustion k)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    let f := G.normalizedPotentialPullback L k ∘ (extChartAt (𝓡 3) z).symm
    let H := G.normalizedPotentialSpacetimeCoefficients L z k
    fderiv ℝ (fderiv ℝ f) x v w =
      fderiv ℝ f x (CoordinateExponential.christoffelBilinear (fun y => H (0, y)) x v w) +
        (H (0, x) v w + deriv (fun t => H (t, x)) 0 v w) /
          (2 * S.potentialGradientScale (q (L.subsequence k))) := by
  let c := extChartAt (𝓡 3) z
  let U := c.target ∩ c.symm ⁻¹' L.exhaustion k
  let e := G.unscaledOriginalEmbedding L k ∘ c.symm
  let eS := L.embedding k ∘ c.symm
  let d := (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M).symm
  let H := fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
    (G.unscaledSourceFlow.shrink.metric p.1).pullbackCoefficients eS p.2
  have hU : IsOpen U :=
    (contMDiffOn_extChartAt_symm (n := ∞) z).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target z) (L.exhaustion_open k)
  have hxU : x ∈ U := ⟨hx, hxk⟩
  have hc (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) z hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hsmall (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ eS y :=
    ((L.embedding_smooth k ⟨c.symm y, hy.2⟩).contMDiffAt).comp y (hc y hy.1)
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U :=
    (G.unscaledOriginalEmbedding_contMDiffOn L k).comp
      ((contMDiffOn_extChartAt_symm (n := ∞) z).mono inter_subset_left) inter_subset_right
  have hi (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U) :
      (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible := by
    have hiE : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (G.unscaledOriginalEmbedding L k) (c.symm y) :=
      (L.embedding_smooth k ⟨c.symm y, hy.2⟩).comp (𝓡 3) M (d.isLocalDiffeomorph _)
    have hiC : (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
      simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
        (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 3) hy.1)
    dsimp only [e]
    rw [mfderiv_comp y (hiE.contMDiffAt.mdifferentiableAt (by simp))
      ((hc y hy.1).mdifferentiableAt (by simp))]
    exact (show (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) (c.symm y)).IsInvertible
      from ⟨hiE.mfderivToContinuousLinearEquiv (by simp), rfl⟩).comp hiC
  have hmetric (t : ℝ) (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U) :
      (G.unscaledSourceFlow.metric t).pullbackCoefficients e y = H (t, y) := by
    ext a b
    change (G.unscaledSourceFlow.metric t).inner (d (eS y))
      (mfderiv (𝓡 3) (𝓡 3) (d ∘ eS) y a)
      (mfderiv (𝓡 3) (𝓡 3) (d ∘ eS) y b) = _
    rw [mfderiv_comp y (d.contMDiff.mdifferentiable (by simp) _)
      ((hsmall y hy).mdifferentiableAt (by simp))]
    rfl
  have hmetric0 : (G.unscaledSourceFlow.metric 0).pullbackCoefficients e =ᶠ[𝓝 x]
      (fun y => H (0, y)) := by
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact hmetric 0 y hy
  have hΓ : CoordinateExponential.christoffelBilinear
      ((G.unscaledSourceFlow.metric 0).pullbackCoefficients e) x =
      CoordinateExponential.christoffelBilinear (fun y => H (0, y)) x := by
    simp only [CoordinateExponential.christoffelBilinear,
      hmetric0.self_of_nhds, hmetric0.fderiv_eq]
  have ht : (fun t => (G.unscaledSourceFlow.metric t).pullbackCoefficients e x) =
      (fun t => H (t, x)) := funext (fun t => hmetric t x hxU)
  have h := G.normalizedPotential_fderiv2_in_parametrization
    (q (L.subsequence k)) hU he hi hxU v w
  rw [hΓ, hmetric0.self_of_nhds, ht] at h
  exact h

end PoincareConjecture.ShrinkingSolitonFlow
