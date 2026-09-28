import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Connection
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter PoincareConjecture
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Curvature.Hypersurface

variable {m n : ℕ}
  {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
  {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))}


theorem hessian_comp_eq_add_secondFundamentalForm
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin m)}
    (hF : ContDiffAt ℝ ∞ F x) (hφ : ContDiffAt ℝ ∞ φ (F x))
    (u v : EuclideanSpace ℝ (Fin m)) :
    D'.hessian (φ ∘ F) x u v =
      D.hessian φ (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) +
        fderiv ℝ φ (F x) (secondFundamentalForm D D' F x u v) := by
  have hFd := hF.differentiableAt (by simp)
  have hφd := hφ.differentiableAt (by simp)
  have hF₂ := (hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hφ₂ := (hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he : fderiv ℝ (φ ∘ F) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ φ (F y)).comp (fderiv ℝ F y) := by
    filter_upwards [(hF.of_le (show 1 ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp),
      hF.continuousAt.eventually
        ((hφ.of_le (show 1 ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp))] with y hyF hyφ
    exact fderiv_comp y (hyφ.differentiableAt (by simp))
      (hyF.differentiableAt (by simp))
  have h₂ : fderiv ℝ (fderiv ℝ (φ ∘ F)) x u v =
      fderiv ℝ (fderiv ℝ φ) (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) +
        fderiv ℝ φ (F x) (fderiv ℝ (fderiv ℝ F) x u v) := by
    have hc := fderiv_clm_comp (hφ₂.comp x hFd) hF₂
    dsimp only [Function.comp_def] at hc
    rw [he.fderiv_eq, hc, fderiv_fun_comp x hφ₂ hFd]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
    abel
  rw [D'.hessian_eq_fderiv_sub_christoffel (hφ.comp x hF),
    D.hessian_eq_fderiv_sub_christoffel hφ, h₂, fderiv_comp x hφd hFd]
  simp only [secondFundamentalForm, covariantHessianMap,
    LeviCivitaData.connectionCoefficient_eq_coordinateChristoffel,
    CoordinateExponential.christoffelBilinear_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sub]
  ring

end Poincare.Geometry.Curvature.Hypersurface

namespace PoincareConjecture.RiemannianMetric.Induced

open Poincare.Geometry.Curvature.Hypersurface

variable {m n : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) L] [IsManifold (𝓡 m) ∞ L]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {h : RiemannianMetric m L}

private theorem chart_symm_mfderiv (x : M) :
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  have he := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at he
  convert! he using 1

private theorem hessian_realized_chart (D : LeviCivitaData g)
    {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (DE : LeviCivitaData gE)
    (x : M)
    (hmetric : ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x), ∀ a b,
      gE.inner y a b = g.inner ((extChartAt (𝓡 n) x).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y a)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y b))
    {φ : M → ℝ} (hφ : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ x)
    (u v : TangentSpace (𝓡 n) x) :
    DE.hessian (φ ∘ (extChartAt (𝓡 n) x).symm) (extChartAt (𝓡 n) x x) u v =
      D.hessian φ x u v := by
  have hp := (extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) x).symm
      (extChartAt (𝓡 n) x x) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hi : ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x),
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target x)] with y hy
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  have he := DE.hessian_comp_of_metric_pullback D hc hi hmetric
    (by simpa only [hp] using hφ) u v
  rw [chart_symm_mfderiv] at he
  change DE.hessian (φ ∘ (extChartAt (𝓡 n) x).symm) (extChartAt (𝓡 n) x x) u v =
    D.hessian φ ((extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x)) u v at he
  erw [hp] at he
  exact he



theorem exists_normal_hessian_correction
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : L → M} (hF : ContMDiff (𝓡 m) (𝓡 n) ∞ F) (x : L)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (mfderiv (𝓡 m) (𝓡 n) F y a) (mfderiv (𝓡 m) (𝓡 n) F y b))
    (u v : TangentSpace (𝓡 m) x) :
    ∃ B : TangentSpace (𝓡 n) (F x),
      (∀ w : TangentSpace (𝓡 m) x,
        g.inner (F x) B (mfderiv (𝓡 m) (𝓡 n) F x w) = 0) ∧
      ∀ (φ : M → ℝ), ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ (F x) →
        D'.hessian (φ ∘ F) x u v =
          D.hessian φ (F x) (mfderiv (𝓡 m) (𝓡 n) F x u)
            (mfderiv (𝓡 m) (𝓡 n) F x v) + g.inner (F x) (D.gradient φ (F x)) B := by
  obtain ⟨gE, DE, hE, DE', hgE, hhE, hind⟩ :=
    exists_induced_metric_in_charts g h hF x hmetric
  let c := extChartAt (𝓡 m) x
  let d := extChartAt (𝓡 n) (F x)
  let FE := immersionInCharts (m := m) (n := n) F x
  have hp : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hq : d.symm (d (F x)) = F x := d.left_inv (mem_extChartAt_source (F x))
  have hFE : FE (c x) = d (F x) := by change d (F (c.symm (c x))) = _; rw [hp]
  have hc : ContMDiffAt (𝓡 m) (𝓡 m) ∞ c.symm (c x) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hd : ContMDiffAt (𝓡 n) (𝓡 n) ∞ d.symm (d (F x)) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) (F x)
      (mem_extChartAt_target (F x))).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target (F x)))
  have hFEc : ContDiffAt ℝ ∞ FE (c x) :=
    (immersionInCharts_eventually_contDiffAt hF x).self_of_nhds
  have hdf : fderiv ℝ FE (c x) = mfderiv (𝓡 m) (𝓡 n) F x := by
    symm
    unfold mfderiv
    simp only [(hF x).mdifferentiableAt (by simp),
      ModelWithCorners.range_eq_univ, fderivWithin_univ]
    rfl
  have hg0 (a b : EuclideanSpace ℝ (Fin n)) :
      gE.inner (FE (c x)) a b = g.inner (F x) a b := by
    rw [hFE, hgE.self_of_nhds]
    change g.inner (d.symm (d (F x)))
      (mfderiv (𝓡 n) (𝓡 n) d.symm (d (F x)) a)
      (mfderiv (𝓡 n) (𝓡 n) d.symm (d (F x)) b) = _
    rw [hq, chart_symm_mfderiv]
    rfl
  let B := secondFundamentalForm DE DE' FE (c x) u v
  refine ⟨B, ?_, ?_⟩
  · intro w
    have hn := secondFundamentalForm_normal DE DE' hFEc hind u v w
    rw [hg0, hdf] at hn
    exact hn
  · intro φ hφ
    have hφq : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ (d.symm (d (F x))) := by
      simpa only [hq] using hφ
    have hφE : ContDiffAt ℝ ∞ (φ ∘ d.symm) (FE (c x)) := by
      rw [hFE]
      exact contMDiffAt_iff_contDiffAt.mp (hφq.comp _ hd)
    have he : ((φ ∘ d.symm) ∘ FE) =ᶠ[𝓝 (c x)] ((φ ∘ F) ∘ c.symm) := by
      have hn : ∀ᶠ y in 𝓝 (c x), F (c.symm y) ∈ d.source := by
        apply (hF.continuous.continuousAt.comp hc.continuousAt).eventually
        change d.source ∈ 𝓝 (F (c.symm (c x)))
        rw [hp]
        exact (isOpen_extChartAt_source (I := 𝓡 n) (F x)).mem_nhds
          (mem_extChartAt_source (F x))
      filter_upwards [hn] with y hy
      exact congrArg φ (d.left_inv hy)
    have hchain := hessian_comp_eq_add_secondFundamentalForm DE DE' hFEc hφE u v
    rw [DE'.hessian_eq_of_eventuallyEq he,
      hessian_realized_chart D' DE' x hhE (hφ.comp x (hF x)), hdf] at hchain
    have ha := hessian_realized_chart D DE (F x) hgE hφ
      (mfderiv (𝓡 m) (𝓡 n) F x u) (mfderiv (𝓡 m) (𝓡 n) F x v)
    rw [hFE] at hchain
    change D'.hessian (φ ∘ F) x u v =
      DE.hessian (φ ∘ d.symm) (d (F x))
        (mfderiv (𝓡 m) (𝓡 n) F x u) (mfderiv (𝓡 m) (𝓡 n) F x v) +
      fderiv ℝ (φ ∘ d.symm) (d (F x)) B at hchain
    rw [ha] at hchain
    have hdφ : fderiv ℝ (φ ∘ d.symm) (d (F x)) B =
        g.inner (F x) (D.gradient φ (F x)) B := by
      rw [D.inner_gradient]
      have heφ := mfderiv_comp (d (F x))
        (hφq.mdifferentiableAt (by simp))
        (hd.mdifferentiableAt (by simp))
      rw [mfderiv_eq_fderiv] at heφ
      have heB := congrArg (fun A => A B) heφ
      change fderiv ℝ (φ ∘ d.symm) (d (F x)) B =
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ) φ (d.symm (d (F x)))
          (mfderiv (𝓡 n) (𝓡 n) d.symm (d (F x)) B) at heB
      rw [chart_symm_mfderiv] at heB
      change fderiv ℝ (φ ∘ d.symm) (d (F x)) B =
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ) φ (d.symm (d (F x))) B at heB
      erw [hq] at heB
      exact heB
    rw [hdφ] at hchain
    exact hchain

end PoincareConjecture.RiemannianMetric.Induced
