import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.ConnectionEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.ConnectionFlux
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.GradientCommutation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.VectorGreen









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem integrable_trace_connection (D : LeviCivitaData g)
    {V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hV : ContDiff ℝ ∞ V) (hc : HasCompactSupport V) :
    Integrable (fun x => LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (D.connection V x).toLinearMap) g.volumeMeasure := by
  have heq (x : EuclideanSpace ℝ (Fin n)) :
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (D.connection V x).toLinearMap =
        ∑ i, WithLp.ofLp (show EuclideanSpace ℝ (Fin n) from
          D.connection V x (EuclideanSpace.basisFun (Fin n) ℝ i)) i := by
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
    rfl
  have hcont : Continuous (fun x => LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (D.connection V x).toLinearMap) := by
    simp_rw [heq]
    apply continuous_finsetSum
    intro i _
    have hVs := contMDiff_vectorSpace_iff_contDiff.mpr hV
    have hi : ContDiff ℝ ∞ (fun x => (show EuclideanSpace ℝ (Fin n) from
        D.connection V x (EuclideanSpace.basisFun (Fin n) ℝ i))) := by
      apply contDiff_iff_contDiffAt.mpr
      intro x
      apply contMDiffAt_vectorSpace_iff_contDiffAt.mp
      exact D.contMDiffAt_covariantDerivativeOnFields
        (contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const) (hVs x)
    exact (EuclideanSpace.proj i).continuous.comp hi.continuous
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact hc
  intro x hx
  by_contra hx'
  have hVs := contMDiff_vectorSpace_iff_contDiff.mpr hV
  exact hx (by simp [D.connection_eq_zero_of_notMem_tsupport
    ((hVs x).mdifferentiableAt (by simp)) hx'])

private theorem trace_connectionFlux_harmonic_gradient (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ ∞ f) (hZ : ContDiff ℝ ∞ Z)
    (hharm : ∀ x ∈ tsupport Z, D.laplacian f =ᶠ[𝓝 x] fun _ => 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (D.connection (D.connectionFlux (D.gradient f) Z) x).toLinearMap =
      D.ricci x (D.gradient f x) (Z x) +
        ∑ i, g.inner x (D.connection (D.gradient f) x (g.orthonormalBasis x i))
          (D.connection Z x (g.orthonormalBasis x i)) := by
  have hfs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.mpr hf
  have hgrad : ContDiff ℝ ∞ (D.gradient f) :=
    contMDiff_vectorSpace_iff_contDiff.mp (D.contMDiff_gradient hfs)
  rw [D.trace_connectionFlux hgrad hZ, Finset.sum_add_distrib,
    D.sum_inner_second_connection_gradient hfs]
  have hz : g.inner x (D.gradient (D.laplacian f) x) (Z x) = 0 := by
    by_cases hx : x ∈ tsupport Z
    · rw [D.inner_gradient, Poincare.mvfderiv_eq_of_eventuallyEq (hharm x hx),
        mvfderiv_const, zero_apply]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [hz, zero_add]



theorem integrable_ricci_harmonic_gradient (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ ∞ f) (hZ : ContDiff ℝ ∞ Z) (hc : HasCompactSupport Z)
    (hharm : ∀ x ∈ tsupport Z, D.laplacian f =ᶠ[𝓝 x] fun _ => 0) :
    Integrable (fun x => D.ricci x (D.gradient f x) (Z x)) g.volumeMeasure := by
  have hfs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.mpr hf
  have hgrad : ContDiff ℝ ∞ (D.gradient f) :=
    contMDiff_vectorSpace_iff_contDiff.mp (D.contMDiff_gradient hfs)
  have hF := D.contDiff_connectionFlux hgrad hZ
  have hFc := D.hasCompactSupport_connectionFlux (D.gradient f) hc
  have hpair := D.integrable_inner_connection (D.contMDiff_gradient hfs)
    (contMDiff_vectorSpace_iff_contDiff.mpr hZ) hc
  have htrace := integrable_trace_connection D hF hFc
  apply (htrace.sub hpair).congr
  exact Eventually.of_forall fun x => by
    change LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (D.connection (D.connectionFlux (D.gradient f) Z) x).toLinearMap -
      (∑ i, g.inner x (D.connection (D.gradient f) x (g.orthonormalBasis x i))
        (D.connection Z x (g.orthonormalBasis x i))) = _
    rw [trace_connectionFlux_harmonic_gradient D hf hZ hharm]
    ring



theorem integral_inner_connection_harmonic_gradient (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ ∞ f) (hZ : ContDiff ℝ ∞ Z) (hc : HasCompactSupport Z)
    (hharm : ∀ x ∈ tsupport Z, D.laplacian f =ᶠ[𝓝 x] fun _ => 0) :
    (∫ x, ∑ i, g.inner x (D.connection (D.gradient f) x (g.orthonormalBasis x i))
      (D.connection Z x (g.orthonormalBasis x i)) ∂g.volumeMeasure) =
      -(∫ x, D.ricci x (D.gradient f x) (Z x) ∂g.volumeMeasure) := by
  have hfs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.mpr hf
  have hgrad : ContDiff ℝ ∞ (D.gradient f) :=
    contMDiff_vectorSpace_iff_contDiff.mp (D.contMDiff_gradient hfs)
  have hF := D.contDiff_connectionFlux hgrad hZ
  have hFc := D.hasCompactSupport_connectionFlux (D.gradient f) hc
  have hpair := D.integrable_inner_connection (D.contMDiff_gradient hfs)
    (contMDiff_vectorSpace_iff_contDiff.mpr hZ) hc
  have hzero := D.integral_trace_connection_eq_zero (hF.of_le (by simp)) hFc
  simp_rw [trace_connectionFlux_harmonic_gradient D hf hZ hharm] at hzero
  rw [integral_add (D.integrable_ricci_harmonic_gradient hf hZ hc hharm) hpair] at hzero
  linarith



theorem integral_inner_connection_gradient_sub (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {X Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : ContDiff ℝ ∞ f) (hX : ContDiff ℝ ∞ X) (hZ : ContDiff ℝ ∞ Z)
    (hc : HasCompactSupport Z)
    (hharm : ∀ x ∈ tsupport Z, D.laplacian f =ᶠ[𝓝 x] fun _ => 0) :
    (∫ x, ∑ i, g.inner x
      (D.connection (fun y => (show EuclideanSpace ℝ (Fin n) from D.gradient f y) - X y)
        x (g.orthonormalBasis x i))
      (D.connection Z x (g.orthonormalBasis x i)) ∂g.volumeMeasure) =
      -(∫ x, D.ricci x (D.gradient f x) (Z x) ∂g.volumeMeasure) -
        ∫ x, ∑ i, g.inner x (D.connection X x (g.orthonormalBasis x i))
          (D.connection Z x (g.orthonormalBasis x i)) ∂g.volumeMeasure := by
  have hfs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.mpr hf
  have hgrad := D.contMDiff_gradient hfs
  have hXf := contMDiff_vectorSpace_iff_contDiff.mpr hX
  have hZf := contMDiff_vectorSpace_iff_contDiff.mpr hZ
  have hsub : ContDiff ℝ ∞ (fun y =>
      (show EuclideanSpace ℝ (Fin n) from D.gradient f y) - X y) :=
    (contMDiff_vectorSpace_iff_contDiff.mp hgrad).sub hX
  have hsubf := contMDiff_vectorSpace_iff_contDiff.mpr hsub
  have heq (x v : EuclideanSpace ℝ (Fin n)) :
      D.connection (fun y => (show EuclideanSpace ℝ (Fin n) from D.gradient f y) - X y) x v =
        D.connection (D.gradient f) x v - D.connection X x v := by
    have h := D.connection.isCovariantDerivativeOnUniv.add
      ((hsubf x).mdifferentiableAt (by simp)) ((hXf x).mdifferentiableAt (by simp))
    have hfun : (fun y => (show EuclideanSpace ℝ (Fin n) from D.gradient f y) - X y) + X =
        (show EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) from D.gradient f) := by
      funext y
      exact sub_add_cancel _ _
    rw [hfun] at h
    have hv := congrArg (fun L => L v) h
    simp only [add_apply] at hv
    convert! (eq_sub_iff_add_eq.mpr hv.symm) using 1
  simp_rw [heq, map_sub, sub_apply, Finset.sum_sub_distrib]
  rw [integral_sub (D.integrable_inner_connection hgrad hZf hc)
    (D.integrable_inner_connection hXf hZf hc),
    D.integral_inner_connection_harmonic_gradient hf hZ hc hharm]

end PoincareConjecture.LeviCivitaData
