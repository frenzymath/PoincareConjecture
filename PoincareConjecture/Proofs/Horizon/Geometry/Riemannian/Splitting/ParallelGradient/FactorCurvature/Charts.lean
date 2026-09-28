import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.FactorCurvature.Gauss
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.CoordinateField
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Charts









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter VectorField
open Poincare.Geometry.Curvature.Hypersurface
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric.FactorCurvature

private theorem inverse_chart_smooth {k : ℕ} {P : Type*} [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) P] [IsManifold (𝓡 k) ∞ P]
    (p : P) {z : EuclideanSpace ℝ (Fin k)}
    (hz : z ∈ (extChartAt (𝓡 k) p).target) :
    ContMDiffAt (𝓡 k) (𝓡 k) ∞ (extChartAt (𝓡 k) p).symm z :=
  (contMDiffWithinAt_extChartAt_symm_target (n := ∞) p hz).contMDiffAt
    (extChartAt_target_mem_nhds' hz)

private theorem inverse_chart_invertible {k : ℕ} {P : Type*} [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) P] [IsManifold (𝓡 k) ∞ P]
    (p : P) {z : EuclideanSpace ℝ (Fin k)}
    (hz : z ∈ (extChartAt (𝓡 k) p).target) :
    (mfderiv (𝓡 k) (𝓡 k) (extChartAt (𝓡 k) p).symm z).IsInvertible := by
  simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
    isInvertible_mfderivWithin_extChartAt_symm hz

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 (n + 1)) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric (n + 1) M} {h : RiemannianMetric n N}




def TotallyGeodesicAt (g : RiemannianMetric (n + 1) M)
    (h : RiemannianMetric n N) (i : N → M) (y : N) : Prop :=
  let c := extChartAt (𝓡 n) y
  let d := extChartAt (𝓡 (n + 1)) (i y)
  let F := immersionInCharts (m := n) (n := n + 1) i y
  ∃ (gE : RiemannianMetric (n + 1) (EuclideanSpace ℝ (Fin (n + 1))))
    (DE : LeviCivitaData gE) (hE : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (DhE : LeviCivitaData hE),
    (∀ᶠ a in 𝓝 (d (i y)), ∀ b e, gE.inner a b e = g.inner (d.symm a)
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm a b)
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm a e)) ∧
    (∀ᶠ a in 𝓝 (c y), ∀ b e, hE.inner a b e = h.inner (c.symm a)
      (mfderiv (𝓡 n) (𝓡 n) c.symm a b) (mfderiv (𝓡 n) (𝓡 n) c.symm a e)) ∧
    (∀ᶠ a in 𝓝 (c y), ∀ b e, hE.inner a b e =
      gE.inner (F a) (fderiv ℝ F a b) (fderiv ℝ F a e)) ∧
    ∀ u v, secondFundamentalForm DE DhE F (c y) u v = 0




theorem totallyGeodesic_and_curvatureTensor_of_orthogonal_parallel_gradient
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {i : N → M} (hi : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ i)
    (hmetric : ∀ y u v, h.inner y u v = g.inner (i y)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) i y u) (mfderiv (𝓡 n) (𝓡 (n + 1)) i y v))
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f)
    (horth : ∀ y u, g.inner (i y) (D.gradient f (i y))
      (mfderiv (𝓡 n) (𝓡 (n + 1)) i y u) = 0)
    (y : N) :
    TotallyGeodesicAt g h i y ∧ ∀ u v w z : TangentSpace (𝓡 n) y,
      Dh.curvatureTensor y u v w z = D.curvatureTensor (i y)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) i y u) (mfderiv (𝓡 n) (𝓡 (n + 1)) i y v)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) i y w) (mfderiv (𝓡 n) (𝓡 (n + 1)) i y z) := by
  obtain ⟨gE, DE, hE, DhE, hgE, hhE, hFE⟩ :=
    exists_induced_metric_in_charts g h hi y (Eventually.of_forall hmetric)
  let c := extChartAt (𝓡 n) y
  let d := extChartAt (𝓡 (n + 1)) (i y)
  let p := c y
  let q := d (i y)
  let F := immersionInCharts (m := n) (n := n + 1) i y
  let G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    mpullback (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm (D.gradient f)
  have hp : c.symm p = y := c.left_inv (mem_extChartAt_source y)
  have hq : d.symm q = i y := d.left_inv (mem_extChartAt_source (i y))
  have hFp : F p = q := by
    change d (i (c.symm p)) = q
    rw [hp]
  have hc := inverse_chart_smooth (k := n) y (mem_extChartAt_target y)
  have hd := inverse_chart_smooth (k := n + 1) (i y) (mem_extChartAt_target (i y))
  have hF : ∀ᶠ a in 𝓝 p, ContDiffAt ℝ ∞ F a :=
    immersionInCharts_eventually_contDiffAt hi y
  have hFcont : ContinuousAt F p := hF.self_of_nhds.continuousAt
  have hci : ∀ᶠ a in 𝓝 p, (mfderiv (𝓡 n) (𝓡 n) c.symm a).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target y)] with a ha
    exact inverse_chart_invertible y ha
  have hdi : ∀ᶠ a in 𝓝 q,
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm a).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target (i y))] with a ha
    exact inverse_chart_invertible (i y) ha
  have hfc : ∀ᶠ a in 𝓝 p, i (c.symm a) ∈ d.source := by
    apply (hi.continuous.continuousAt.comp hc.continuousAt).eventually
    change d.source ∈ 𝓝 (i (c.symm p))
    rw [hp]
    exact (isOpen_extChartAt_source (I := 𝓡 (n + 1)) (i y)).mem_nhds
      (mem_extChartAt_source (i y))
  have hcomm : d.symm ∘ F =ᶠ[𝓝 p] i ∘ c.symm := by
    filter_upwards [hfc] with a ha
    exact d.left_inv ha
  have hFt : ∀ᶠ a in 𝓝 p, F a ∈ d.target := by
    filter_upwards [hfc] with a ha
    exact d.map_source ha
  have hgnear : ∀ᶠ a in 𝓝 p, ∀ b e : EuclideanSpace ℝ (Fin (n + 1)),
      gE.inner (F a) b e = g.inner (d.symm (F a))
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm (F a) b)
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm (F a) e) := by
    have ht : ∀ᶠ a in 𝓝 (F p), ∀ b e : EuclideanSpace ℝ (Fin (n + 1)),
        gE.inner a b e = g.inner (d.symm a)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm a b)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm a e) := by
      rw [hFp]
      convert! hgE
    exact hFcont.eventually ht
  have hdF (a : EuclideanSpace ℝ (Fin n))
      (hca : a ∈ c.target) (hfa : F a ∈ d.target)
      (hFa : ContDiffAt ℝ ∞ F a)
      (hcoma : d.symm ∘ F =ᶠ[𝓝 a] i ∘ c.symm)
      (b : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm (F a) (fderiv ℝ F a b) =
        mfderiv (𝓡 n) (𝓡 (n + 1)) i (c.symm a) (mfderiv (𝓡 n) (𝓡 n) c.symm a b) := by
    have he := hcoma.mfderiv_eq (I := 𝓡 n) (I' := 𝓡 (n + 1))
    rw [mfderiv_comp a ((inverse_chart_smooth (i y) hfa).mdifferentiableAt (by simp))
      (hFa.differentiableAt (by simp)).mdifferentiableAt,
      mfderiv_comp a (hi.mdifferentiable (by simp) _)
        ((inverse_chart_smooth y hca).mdifferentiableAt (by simp))] at he
    have hea := congrArg (fun A => A b) he
    change mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm (F a)
      (mfderiv (𝓡 n) (𝓡 (n + 1)) F a b) =
      mfderiv (𝓡 n) (𝓡 (n + 1)) i (c.symm a) (mfderiv (𝓡 n) (𝓡 n) c.symm a b) at hea
    rw [mfderiv_eq_fderiv] at hea
    exact hea
  have hGmap (a : EuclideanSpace ℝ (Fin (n + 1))) (ha : a ∈ d.target) :
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm a (G a) = D.gradient f (d.symm a) := by
    exact (inverse_chart_invertible (i y) ha).self_apply_inverse _
  have hGd : DifferentiableAt ℝ G q :=
    (contDiffAt_mpullback_gradient hf (i y) (mem_extChartAt_target (i y))).differentiableAt
      (by simp)
  have hνd : DifferentiableAt ℝ (G ∘ F) p :=
    (hFp.symm ▸ hGd).comp p (hF.self_of_nhds.differentiableAt (by simp))
  have hunit : gE.inner (F p) (G (F p)) (G (F p)) = 1 := by
    rw [hFp, hgE.self_of_nhds, hGmap q (mem_extChartAt_target (i y))]
    exact hu _
  have hnormal : ∀ᶠ a in 𝓝 p, ∀ b, gE.inner (F a) ((G ∘ F) a) (fderiv ℝ F a b) = 0 := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target y), hFt, hF,
      hcomm.eventually_nhds, hgnear] with a hca hfa hFa hcoma hga b
    rw [Function.comp_apply, hga, hGmap (F a) hfa, hdF a hca hfa hFa hcoma]
    have he : d.symm (F a) = i (c.symm a) := hcoma.self_of_nhds
    rw [he]
    exact horth _ _
  have hparallel : ∀ a, covariantDerivativeAlongMap DE F (G ∘ F) p a = 0 := by
    intro a
    have he := DE.connection_mpullback_of_metric_pullback D hd hdi hgE
      ((D.contMDiff_gradient hf _).mdifferentiableAt (by simp)) (fderiv ℝ F p a)
    rw [connection_gradient_eq_zero_of_hasZeroHessian hf hz, map_zero] at he
    change DE.connection G q (fderiv ℝ F p a) = 0 at he
    rw [DE.connection_eq_fderiv_add hGd] at he
    rw [covariantDerivativeAlongMap, fderiv_comp p (hFp.symm ▸ hGd)
      (hF.self_of_nhds.differentiableAt (by simp)), ContinuousLinearMap.comp_apply,
      Function.comp_apply, hFp]
    exact he
  refine ⟨⟨gE, DE, hE, DhE, hgE, hhE, hFE,
    fun a b => secondFundamentalForm_eq_zero_of_parallel_normal DE DhE
      hF.self_of_nhds hνd hFE hunit hnormal hparallel a b⟩, ?_⟩
  intro u v w z
  have hcurv (a b e k : EuclideanSpace ℝ (Fin n)) :
      DhE.curvatureTensor p a b e k = DE.curvatureTensor (F p)
        (fderiv ℝ F p a) (fderiv ℝ F p b) (fderiv ℝ F p e) (fderiv ℝ F p k) :=
    curvatureTensor_eq_of_parallel_normal DE DhE hF hνd hFE hunit hnormal hparallel a b e k
  have hs (a b e k : EuclideanSpace ℝ (Fin n)) :=
    DhE.curvatureTensor_eq_pullback_euclidean Dh hc hci hhE a b e k
  have ha (a b e k : EuclideanSpace ℝ (Fin (n + 1))) :=
    DE.curvatureTensor_eq_pullback_euclidean D hd hdi hgE a b e k
  have hcpoint := hci.self_of_nhds
  let C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) c.symm p
  have hC : C.IsInvertible := by convert! hcpoint
  have hCinv (a : EuclideanSpace ℝ (Fin n)) : C (C.inverse a) = a :=
    hC.self_apply_inverse a
  have hsource := hs (C.inverse u) (C.inverse v) (C.inverse w) (C.inverse z)
  have hrest := hcurv (C.inverse u) (C.inverse v) (C.inverse w) (C.inverse z)
  rw [hsource, hFp, ha] at hrest
  have hcomp (a : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm q (fderiv ℝ F p (C.inverse a)) =
        mfderiv (𝓡 n) (𝓡 (n + 1)) i y a := by
    rw [← hFp, hdF p (mem_extChartAt_target y) (hFp.symm ▸ mem_extChartAt_target (i y))
      hF.self_of_nhds hcomm]
    change mfderiv (𝓡 n) (𝓡 (n + 1)) i (c.symm p) (C (C.inverse a)) = _
    erw [hCinv, hp]
  change Dh.curvatureTensor (c.symm p) (C (C.inverse u)) (C (C.inverse v))
    (C (C.inverse w)) (C (C.inverse z)) = D.curvatureTensor (d.symm q)
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm q (fderiv ℝ F p (C.inverse u)))
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm q (fderiv ℝ F p (C.inverse v)))
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm q (fderiv ℝ F p (C.inverse w)))
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.symm q (fderiv ℝ F p (C.inverse z))) at hrest
  simp only [hcomp, hCinv] at hrest
  erw [hp, hq] at hrest
  exact hrest

end PoincareConjecture.RiemannianMetric.FactorCurvature
