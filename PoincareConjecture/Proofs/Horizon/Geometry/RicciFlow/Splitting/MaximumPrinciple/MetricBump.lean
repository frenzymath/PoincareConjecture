import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.ChartOperator
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.Barrier.Jets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.Barrier.CoefficientBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple

open Barrier

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def radialQuadratic (g : RiemannianMetric n M) (p : M)
    (y d : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ⟪d, (chartMetric g p y).inverse (EuclideanSpace.proj i)⟫_ℝ *
    ⟪d, EuclideanSpace.basisFun (Fin n) ℝ i⟫_ℝ

def radialTrace (g : RiemannianMetric n M) (p : M)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
    (chartMetric g p y).inverse (EuclideanSpace.proj i)⟫_ℝ

def radialDrift (g : RiemannianMetric n M) (p : M)
    (y d : EuclideanSpace ℝ (Fin n)) : ℝ := -⟪d, chartDrift g p y⟫_ℝ

def chartBump (p : M) (rho C a : ℝ)
    (gamma : ℝ → EuclideanSpace ℝ (Fin n)) (x : M) (t : ℝ) : ℝ :=
  movingBump rho C a gamma t (extChartAt (𝓡 n) p x)

theorem contMDiffOn_chartBump (p : M) (rho C a : ℝ)
    (gamma : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => chartBump p rho C a gamma x t)
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
  intro x hx
  exact ((contMDiffAt_iff_contDiffAt.mpr
    (contDiff_movingBump_space rho C a gamma t).contDiffAt).comp x
      (contMDiffAt_extChartAt' hx)).contMDiffWithinAt

omit [IsManifold (𝓡 n) ∞ M] in
theorem hasDerivAt_chartBump (p : M) (rho C a : ℝ)
    {gamma : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    {velocity : EuclideanSpace ℝ (Fin n)} (hg : HasDerivAt gamma velocity t) (x : M) :
    HasDerivAt (chartBump p rho C a gamma x)
      (timeJet rho C a gamma t (extChartAt (𝓡 n) p x) velocity) t :=
  hasDerivAt_movingBump_time rho C a hg (extChartAt (𝓡 n) p x)

private theorem second_fderiv_movingBump (rho C a : ℝ)
    (gamma : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (y v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (movingBump rho C a gamma t)) y v w =
      secondSpaceJet rho C a gamma t y w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (movingBump rho C a gamma t)) y :=
    ((contDiff_movingBump_space rho C a gamma t).fderiv_right
      (m := ∞) (by simp)).differentiable (by simp) y
  have h := fderiv_spaceJet rho C a gamma t y w v
  rw [fderiv_clm_apply hd (differentiableAt_const w)] at h
  simpa using h

theorem chartOperator_movingBump (g : RiemannianMetric n M) (p : M)
    (rho C a : ℝ) (gamma : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    chartOperator g p (movingBump rho C a gamma t) y =
      Real.exp (-C * (t - a)) *
        (4 * profileSecond (ballGap rho (gamma t) y) *
            radialQuadratic g p y (y - gamma t) -
          2 * profileFirst (ballGap rho (gamma t) y) *
            (radialTrace g p y + radialDrift g p y (y - gamma t))) := by
  have hsum : (∑ i, fderiv ℝ (fderiv ℝ (movingBump rho C a gamma t)) y
      (EuclideanSpace.basisFun (Fin n) ℝ i)
      ((chartMetric g p y).inverse (EuclideanSpace.proj i))) =
      Real.exp (-C * (t - a)) *
        (4 * profileSecond (ballGap rho (gamma t) y) *
          radialQuadratic g p y (y - gamma t) -
        2 * profileFirst (ballGap rho (gamma t) y) * radialTrace g p y) := by
    simp only [second_fderiv_movingBump, secondSpaceJet, radialQuadratic, radialTrace,
      mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold chartOperator
  rw [hsum, fderiv_movingBump]
  unfold spaceJet radialDrift
  ring

theorem laplacian_chartBump {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (p : M) (rho C a : ℝ) (gamma : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ)
    {x : M} (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    D.laplacian (fun z => chartBump p rho C a gamma z t) x =
      chartOperator g p (movingBump rho C a gamma t) (extChartAt (𝓡 n) p x) := by
  have hxs : x ∈ (extChartAt (𝓡 n) p).source := by simpa only [extChartAt_source] using hx
  have hy := (extChartAt (𝓡 n) p).map_source hxs
  have hi := (extChartAt (𝓡 n) p).left_inv hxs
  have hf := (contMDiffOn_chartBump p rho C a gamma t).contMDiffAt
    ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hx)
  have hlap := laplacian_in_chart D p hy (by simpa only [hi] using hf)
  rw [hi] at hlap
  rw [hlap]
  apply chartOperator_congr
  filter_upwards [extChartAt_target_mem_nhds' hy] with z hz
  simp only [Function.comp_apply, chartBump, (extChartAt (𝓡 n) p).right_inv hz]

theorem chart_heat_residual {g : ℝ → RiemannianMetric n M}
    (D : ∀ t, LeviCivitaData (g t)) (p : M) (rho C a : ℝ)
    {gamma : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    {velocity : EuclideanSpace ℝ (Fin n)} (hg : HasDerivAt gamma velocity t)
    {x : M} (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    (D t).laplacian (fun z => chartBump p rho C a gamma z t) x -
      deriv (chartBump p rho C a gamma x) t =
      Real.exp (-C * (t - a)) *
        (C * expNegInvGlue (ballGap rho (gamma t) (extChartAt (𝓡 n) p x)) +
          4 * profileSecond (ballGap rho (gamma t) (extChartAt (𝓡 n) p x)) *
            radialQuadratic (g t) p (extChartAt (𝓡 n) p x) (extChartAt (𝓡 n) p x - gamma t) -
          2 * profileFirst (ballGap rho (gamma t) (extChartAt (𝓡 n) p x)) *
            (radialTrace (g t) p (extChartAt (𝓡 n) p x) +
              radialDrift (g t) p (extChartAt (𝓡 n) p x) (extChartAt (𝓡 n) p x - gamma t) +
              ⟪extChartAt (𝓡 n) p x - gamma t, velocity⟫_ℝ)) := by
  rw [laplacian_chartBump (D t) p rho C a gamma t hx,
    (hasDerivAt_chartBump p rho C a hg x).deriv, chartOperator_movingBump]
  unfold timeJet
  ring

end PoincareConjecture.RicciFlow.Splitting.MaximumPrinciple
