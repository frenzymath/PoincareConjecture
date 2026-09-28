import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.WeakFlux
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Volume
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.ForwardDivergence
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.AdjointIdentity
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Extension.FiniteDimension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei

theorem density_drift_balance {z : Spacetime n} (hz : z ∈ domain J e) (i : Fin n) :
    drift F e i z * density F e z =
      ∑ j, Canonical.spatialDeriv j
        (fun y => principal F e i j y * density F e y) z := by
  have heq (j) : (fun y => principal F e i j y * density F e y) =ᶠ[𝓝 z]
      weightedPrincipal F e j i := by
    filter_upwards [(isOpen_domain e).mem_nhds hz] with y hy
    rw [weightedPrincipal_eq, principal_symm F e he hei hy.1]
    exact mul_comm _ _
  have hd (j) : Canonical.spatialDeriv j
      (fun y => principal F e i j y * density F e y) z =
      Canonical.spatialDeriv j (weightedPrincipal F e j i) z := by
    exact congrArg (fun L : Spacetime n →L[ℝ] ℝ => L (Canonical.spatialDirection j))
      (heq j).fderiv_eq
  simp only [hd]
  dsimp only [drift]
  field_simp [(density_pos F e he hei hz.1).ne']

theorem divergence_flux_eq_laplacian_of_contDiffOn
    {U : Set (Spacetime n)} (hU : IsOpen U) (hUD : U ⊆ domain J e)
    {u : Spacetime n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    {z : Spacetime n} (hz : z ∈ U) :
    (∑ i, Canonical.spatialDeriv i
      (fun y => ∑ j, weightedPrincipal F e i j y * Canonical.spatialDeriv j u y) z) =
      density F e z * (F.connection (-z.2)).laplacian
        (fun y => u (e.symm y, z.2)) (e z.1) := by
  obtain ⟨v, hv, hvu⟩ := Poincare.Analysis.exists_global_contDiff_germ_finiteDimension hU hu hz
  have hd (j) : Canonical.spatialDeriv j v =ᶠ[𝓝 z] Canonical.spatialDeriv j u := by
    filter_upwards [hvu.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : Spacetime n →L[ℝ] ℝ => L (Canonical.spatialDirection j)) hy
  have hflux (i) :
      (fun y => ∑ j, weightedPrincipal F e i j y * Canonical.spatialDeriv j v y) =ᶠ[𝓝 z]
      (fun y => ∑ j, weightedPrincipal F e i j y * Canonical.spatialDeriv j u y) := by
    filter_upwards [Filter.eventually_all.mpr hd] with y hy
    simp only [hy]
  have hsum : (∑ i, Canonical.spatialDeriv i
      (fun y => ∑ j, weightedPrincipal F e i j y * Canonical.spatialDeriv j v y) z) =
      ∑ i, Canonical.spatialDeriv i
        (fun y => ∑ j, weightedPrincipal F e i j y * Canonical.spatialDeriv j u y) z := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun L : Spacetime n →L[ℝ] ℝ => L (Canonical.spatialDirection i))
      (hflux i).fderiv_eq
  have hmap : ContinuousAt (fun y : M => (e.symm y, z.2)) (e z.1) :=
    (e.continuousAt_symm (e.map_source (hUD hz).1)).prodMk continuousAt_const
  have hs : (fun y => v (e.symm y, z.2)) =ᶠ[𝓝 (e z.1)]
      (fun y => u (e.symm y, z.2)) := by
    have hmap' : Tendsto (fun y : M => (e.symm y, z.2)) (𝓝 (e z.1)) (𝓝 z) := by
      simpa only [ContinuousAt, e.left_inv (hUD hz).1, Prod.eta] using hmap
    exact hvu.comp_tendsto hmap'
  rw [← hsum, divergence_testFlux_eq_laplacian F e he hei hv (hUD hz),
    (F.connection (-z.2)).laplacian_eq_of_eventuallyEq hs]

theorem forward_operator_density_mul
    {U : Set (Spacetime n)} (hU : IsOpen U) (hUD : U ⊆ domain J e)
    {u : Spacetime n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    {z : Spacetime n} (hz : z ∈ U) :
    (Canonical.forwardCoefficients (principal F e) (drift F e)).operator
      (fun y => density F e y * u y) z =
      density F e z * (Canonical.timeDeriv u z -
        (F.connection (-z.2)).laplacian (fun y => u (e.symm y, z.2)) (e z.1) +
        (F.connection (-z.2)).scalarCurvature (e z.1) * u z) := by
  have hρ := (contDiffOn_density F e he hei).mono hUD
  rw [Canonical.forwardCoefficients_operator_weighted hU
    (fun i j => (contDiffOn_principal F e he hei i j).mono hUD)
    (fun i => (contDiffOn_drift F e he hei i).mono hUD) hρ hu
    (fun y hy i => density_drift_balance F e he hei (hUD hy) i) hz]
  have htime : Canonical.timeDeriv (fun y => density F e y * u y) z =
      Canonical.timeDeriv (density F e) z * u z +
        density F e z * Canonical.timeDeriv u z := by
    rw [Canonical.timeDeriv, fderiv_fun_mul
      ((hρ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
      ((hu.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))]
    simp only [add_apply, smul_apply, smul_eq_mul, Canonical.timeDeriv]
    ring
  have hdiv := divergence_flux_eq_laplacian_of_contDiffOn F e he hei hU hUD hu hz
  simp only [weightedPrincipal_eq] at hdiv
  rw [htime, timeDeriv_density F e he hei (hUD hz), hdiv]
  ring



theorem heat_equation_of_smooth_weak_pairing
    {U : Set (Spacetime n)} (hU : IsOpen U) (hUD : U ⊆ domain J e)
    {u : Spacetime n → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hweak : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ z in U, density F e z * u z *
        (-Canonical.timeDeriv φ z - (F.connection (-z.2)).laplacian
          (fun y => φ (e.symm y, z.2)) (e z.1))) = 0)
    {z : Spacetime n} (hz : z ∈ U) :
    Canonical.timeDeriv u z -
      (F.connection (-z.2)).laplacian (fun y => u (e.symm y, z.2)) (e z.1) +
      (F.connection (-z.2)).scalarCurvature (e z.1) * u z = 0 := by
  let C := Canonical.forwardCoefficients (principal F e) (drift F e)
  let w := fun z => density F e z * u z
  have hw : ContDiffOn ℝ ∞ w U := ((contDiffOn_density F e he hei).mono hUD).mul hu
  have hC : C.IsSmoothOn U := Canonical.forwardCoefficients_smooth hU
    (fun i j => (contDiffOn_principal F e he hei i j).mono hUD)
    (fun i => (contDiffOn_drift F e he hei i).mono hUD)
  have hsol : Canonical.WeakSolutionOn C w U := by
    refine ⟨hw.continuousOn.locallyIntegrableOn hU.measurableSet, ?_⟩
    intro φ hφ hφc hφU
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [Canonical.Coefficients.adjoint_eq_zero_of_notMem_tsupport C φ
        (fun hs => hy (hφU hs)), mul_zero])]
    convert hweak φ hφ hφc hφU using 1
    apply setIntegral_congr_fun hU.measurableSet
    intro y hy
    dsimp only [w, C]
    rw [forwardCoefficients_adjoint_eq_coordinateLaplacian F e he hei hφ (hUD hy)]
  have hop := (Canonical.weakSolutionOn_iff_operator_eq_zero hU C hC hw).mp hsol z hz
  rw [forward_operator_density_mul F e he hei hU hUD hu hz] at hop
  exact (mul_eq_zero.mp hop).resolve_left (density_pos F e he hei (hUD hz).1).ne'

end PoincareConjecture.RicciFlow.BackwardCoordinates
