import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.MinimalGaussBound
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Charts
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Intrinsic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation
open Poincare.Geometry.Curvature.Hypersurface

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {h : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))}

theorem m64_harmonic_chart_gaussian_le_sectional
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {f : EuclideanSpace ℝ (Fin 2) → M} {p : EuclideanSpace ℝ (Fin 2)}
    (hf : ∀ᶠ q in 𝓝 p, ContMDiffAt (𝓡 2) (𝓡 n) ∞ f q)
    (hmetric : ∀ᶠ q in 𝓝 p, ∀ a b, h.inner q a b =
      g.inner (f q) (mfderiv (𝓡 2) (𝓡 n) f q a) (mfderiv (𝓡 2) (𝓡 n) f q b))
    (u v : EuclideanSpace ℝ (Fin 2))
    (hu : h.inner p u u = 1) (hv : h.inner p v v = 1) (huv : h.inner p u v = 0)
    (hharm :
      let c := extChartAt (𝓡 n) (f p)
      let F := c ∘ f
      let B := g.pullbackCoefficients c.symm
      covDerivAlong (christoffelBilinear B) F (fun q => fderiv ℝ F q u) u p +
        covDerivAlong (christoffelBilinear B) F (fun q => fderiv ℝ F q v) v p = 0) :
    Dh.scalarCurvature p / 2 ≤
      D.sectionalCurvature (f p) (mfderiv (𝓡 2) (𝓡 n) f p u)
        (mfderiv (𝓡 2) (𝓡 n) f p v) := by
  let c := extChartAt (𝓡 n) (f p)
  let F := c ∘ f
  let B := g.pullbackCoefficients c.symm
  have hc (q : EuclideanSpace ℝ (Fin 2)) (hq : f q ∈ c.source) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (f q) :=
    contMDiffAt_extChartAt' (by simpa only [c, extChartAt_source] using hq)
  have hchart : ∀ᶠ q in 𝓝 p, f q ∈ c.source :=
    hf.self_of_nhds.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (f p)).mem_nhds (mem_extChartAt_source (f p)))
  have hF : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ ∞ F q := by
    filter_upwards [hf, hchart] with q hq hqc
    exact contMDiffAt_iff_contDiffAt.mp ((hc q hqc).comp q hq)
  have hdu (q : EuclideanSpace ℝ (Fin 2))
      (hq : ContMDiffAt (𝓡 2) (𝓡 n) ∞ f q) (hqc : f q ∈ c.source)
      (w : EuclideanSpace ℝ (Fin 2)) :
      fderiv ℝ F q w = mfderiv (𝓡 n) (𝓡 n) c (f q) (mfderiv (𝓡 2) (𝓡 n) f q w) := by
    have hd := mfderiv_comp q ((hc q hqc).mdifferentiableAt (by simp))
      (hq.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hd
    exact congrArg (fun L => L w) hd
  obtain ⟨gE, DE, hgE⟩ := LeviCivitaData.exists_chart_metric g (f p)
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 (F p)] B := by
    filter_upwards [hgE] with y hy
    ext a b
    exact hy a b
  have hsource : ∀ᶠ q in 𝓝 p, ∀ a b, h.inner q a b =
      gE.inner (F q) (fderiv ℝ F q a) (fderiv ℝ F q b) := by
    filter_upwards [hmetric, hf, hchart, hF.self_of_nhds.continuousAt.eventually hB]
      with q hq hqf hqc hqB a b
    change h.inner q a b = gE.euclideanCoefficients (F q)
      (fderiv ℝ F q a) (fderiv ℝ F q b)
    rw [hqB, hdu q hqf hqc a, hdu q hqf hqc b]
    exact (hq a b).trans (chartCoefficients_apply g (f p) hqc _ _).symm
  have hGamma : DE.connectionCoefficient (F p) = christoffelBilinear B (F p) := by
    ext a b
    rw [DE.connectionCoefficient_eq_coordinateChristoffel, christoffelBilinear_apply]
    simp only [coordinateChristoffel, hB.self_of_nhds, hB.fderiv_eq]
  have hcov (w : EuclideanSpace ℝ (Fin 2)) :
      covariantHessianMap DE F p w w =
        covDerivAlong (christoffelBilinear B) F (fun q => fderiv ℝ F q w) w p := by
    rw [← covariantDerivativeAlongMap_fderiv_const DE hF.self_of_nhds,
      covariantDerivativeAlongMap, covDerivAlong_def, hGamma]
  have hbound := m64_harmonic_surface_gaussian_le_sectional DE Dh hF hsource u v hu hv huv
    (by rw [hcov, hcov]; exact hharm)
  have hci : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (F p) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) (f p)
      (mem_extChartAt_target (f p))).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target (f p)))
  have hinv : ∀ᶠ y in 𝓝 (F p), (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target (f p))] with y hy
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  have hid := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := 𝓡 n) (mem_extChartAt_source (f p))
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hid
  have hinverse (w : EuclideanSpace ℝ (Fin 2)) :
      mfderiv (𝓡 n) (𝓡 n) c.symm (F p) (fderiv ℝ F p w) =
        mfderiv (𝓡 2) (𝓡 n) f p w := by
    rw [hdu p hf.self_of_nhds hchart.self_of_nhds w]
    exact congrArg (fun L => L (mfderiv (𝓡 2) (𝓡 n) f p w)) hid
  have hsec := DE.sectionalCurvature_eq_pullback_euclidean D hci hinv hgE
    (fderiv ℝ F p u) (fderiv ℝ F p v)
  rw [hinverse, hinverse] at hsec
  have hpoint : c.symm (F p) = f p := c.left_inv (mem_extChartAt_source (f p))
  have hsec' : DE.sectionalCurvature (F p) (fderiv ℝ F p u) (fderiv ℝ F p v) =
      D.sectionalCurvature (f p) (mfderiv (𝓡 2) (𝓡 n) f p u)
        (mfderiv (𝓡 2) (𝓡 n) f p v) := by
    exact hsec.trans (congrArg (fun y => D.sectionalCurvature y
      (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 2) (𝓡 n) f p u)
      (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 2) (𝓡 n) f p v)) hpoint)
  exact hbound.trans_eq hsec'

end PoincareConjecture
