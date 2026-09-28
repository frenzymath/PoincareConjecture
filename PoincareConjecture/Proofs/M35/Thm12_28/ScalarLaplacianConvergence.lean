import PoincareConjecture.Proofs.M35.Thm12_28.ScalarGradientConvergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Laplacian.Harmonic

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M35

local notation:max "E" n:max => EuclideanSpace ℝ (Fin n)
local notation:max "G" n:max => E n →L[ℝ] E n →L[ℝ] ℝ

theorem scalar_second_fderiv_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p : E n)
    (hjet : ∀ m ≤ 4, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => fderiv ℝ (fderiv ℝ (Dseq k).scalarCurvature) (pseq k)) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ D.scalarCurvature) p)) := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
  intro i
  apply Poincare.Analysis.tendsto_continuousLinearMap_of_basis b
  intro j
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E n) ℝ
    (fun a => if a = 0 then b i else b j)).continuous.continuousAt.tendsto.comp
      (scalarCurvature_jets_tendsto_of_metric_jets Dseq D pseq p 2 hjet)
  simpa [Function.comp_def, iteratedFDeriv_two_apply] using h

private theorem connection_tendsto_moving_vector {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p u : E n) {vseq : ℕ → E n} {v : E n}
    (hzero : Tendsto (fun k => (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (g.euclideanCoefficients p)))
    (hone : Tendsto (fun k => fderiv ℝ (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (fderiv ℝ g.euclideanCoefficients p)))
    (hv : Tendsto vseq atTop (𝓝 v)) :
    Tendsto (fun k => (Dseq k).euclideanConnection u (vseq k) (pseq k)) atTop
      (𝓝 (D.euclideanConnection u v p)) := by
  have hi : (g.euclideanCoefficients p).IsInvertible := by convert! g.inner_isInvertible p
  have hinv := (hi.contDiffAt_map_inverse (n := 0)).continuousAt.tendsto.comp hzero
  have hK : Continuous (fun z : (E n →L[ℝ] G n) × E n =>
      metricKoszulCovector z.1 u z.2) := by
    have hf : Continuous (fun C : G n => C.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).continuous
    have hf' : Continuous (fun C : E n →L[ℝ] G n => C.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) (E n →L[ℝ] ℝ)).continuous
    unfold metricKoszulCovector
    fun_prop
  have hcov := hK.continuousAt.tendsto.comp (hone.prodMk_nhds hv)
  simp_rw [LeviCivitaData.euclideanConnection, LeviCivitaData.connection_const_eq_inverse]
  exact (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    (hinv.prodMk_nhds hcov)

theorem scalar_laplacian_tendsto_of_metric_jets {n : ℕ}
    {gseq : ℕ → RiemannianMetric n (E n)} {g : RiemannianMetric n (E n)}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → E n) (p : E n)
    (hjet : ∀ m ≤ 4, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m g.euclideanCoefficients p))) :
    Tendsto (fun k => (Dseq k).laplacian (Dseq k).scalarCurvature (pseq k)) atTop
      (𝓝 (D.laplacian D.scalarCurvature p)) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hzero : Tendsto (fun k => (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (g.euclideanCoefficients p)) := by
    have h := ((continuousMultilinearCurryFin0 ℝ (E n) (G n)).continuous.tendsto _).comp
      (hjet 0 (by omega))
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hone : Tendsto (fun k => fderiv ℝ (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (fderiv ℝ g.euclideanCoefficients p)) := by
    let C := continuousMultilinearCurryFin1 ℝ (E n) (G n)
    have heq (f : E n → G n) (y : E n) :
        C (iteratedFDeriv ℝ 1 f y) = fderiv ℝ f y := by
      ext v
      simp [C, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    have h := (C.continuous.tendsto _).comp (hjet 1 (by omega))
    simpa only [Function.comp_def, heq] using h
  have hdf := scalar_fderiv_tendsto_of_metric_jets Dseq D pseq p
    (fun m hm => hjet m (by omega))
  have hdd := scalar_second_fderiv_tendsto_of_metric_jets Dseq D pseq p hjet
  have hi : (g.euclideanCoefficients p).IsInvertible := by convert! g.inner_isInvertible p
  have hinv := (hi.contDiffAt_map_inverse (n := 0)).continuousAt.tendsto.comp hzero
  have hdual (i : Fin n) :=
    ((ContinuousLinearMap.apply ℝ (E n) (EuclideanSpace.proj (𝕜 := ℝ) i)).continuous.tendsto
      ((g.euclideanCoefficients p).inverse)).comp hinv
  have hddir (i : Fin n) :=
    ((ContinuousLinearMap.apply ℝ (E n →L[ℝ] ℝ) (b i)).continuous.tendsto _).comp hdd
  have hterm (i : Fin n) :=
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      ((hddir i).prodMk_nhds (hdual i))
  have hconn (i : Fin n) := connection_tendsto_moving_vector Dseq D pseq p (b i)
    hzero hone (hdual i)
  have heq (g' : RiemannianMetric n (E n)) (D' : LeviCivitaData g') (x : E n) :
      D'.laplacian D'.scalarCurvature x =
        (∑ i, fderiv ℝ (fderiv ℝ D'.scalarCurvature) x (b i)
          ((g'.euclideanCoefficients x).inverse (EuclideanSpace.proj i))) -
        fderiv ℝ D'.scalarCurvature x (∑ i, D'.euclideanConnection (b i)
          ((g'.euclideanCoefficients x).inverse (EuclideanSpace.proj i)) x) := by
    rw [D'.laplacian_eq_sum_fderiv_sub_christoffel (scalarCurvature_contDiffAt_euclidean D' x)]
    simp only [b, LeviCivitaData.euclideanConnection, LeviCivitaData.connection_const_eq_inverse]
    rfl
  simp_rw [heq]
  exact (tendsto_finsetSum Finset.univ (fun i _ => hterm i)).sub
    ((continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (hdf.prodMk_nhds (tendsto_finsetSum Finset.univ (fun i _ => hconn i))))

end PoincareConjecture.M35
