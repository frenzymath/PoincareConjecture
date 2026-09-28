import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Regularity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem apply_eq_sum_coordinates
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, L (EuclideanSpace.basisFun (Fin n) ℝ i) * v i := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    mul_comm] using h.symm



theorem integral_mul_laplacian_chart_density
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ e.target) :
    (∫ x in e.source, u (e x) * D.laplacian v (e x) * g.pullbackVolumeDensity e x) =
      -(∫ x in e.source, g.inner (e x) (D.gradient u (e x)) (D.gradient v (e x)) *
        g.pullbackVolumeDensity e x) := by
  let U := chartPullback e u
  let V : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x =>
    g.pullbackVolumeDensity e x * WithLp.ofLp (mpullback (𝓡 n) (𝓡 n) e (D.gradient v) x) i
  have hU : ContDiff ℝ ∞ U := contDiff_chartPullback e he hu hc hs
  have hUc : HasCompactSupport U := hasCompactSupport_chartPullback e hc hs
  have hUs : tsupport U ⊆ e.source := tsupport_chartPullback_subset_source e hc hs
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv (x) (hx : x ∈ e.source) : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible :=
    ⟨hD.mfderiv hx, rfl⟩
  have hV (i) (x) (hx : x ∈ tsupport U) : ContDiffAt ℝ 1 (V i) x := by
    have hx' := hUs hx
    have hef := he.contMDiffAt (e.open_source.mem_nhds hx')
    have hρ := (g.contDiffAt_pullbackVolumeDensity hef (hD.mfderiv_injective hx')).1
    have hgrad := (D.contMDiffAt_gradient (hv (e x))).mpullback_vectorField_preimage
      hef (hinv x hx') (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
    have hvec : ContDiffAt ℝ ∞ (mpullback (𝓡 n) (𝓡 n) e (D.gradient v)) x := by
      exact contMDiffAt_iff_contDiffAt.mp (by simpa using (Bundle.contMDiffAt_totalSpace.mp hgrad).2)
    exact (hρ.mul ((EuclideanSpace.proj i).contDiff.contDiffAt.comp x hvec)).of_le
      (by norm_cast : (1 : ℕ∞ω) ≤ ∞)
  have hparts := Poincare.integral_mul_coordinate_divergence (hU.of_le (by simp)) hUc hV
  have hleft (x) (hx : x ∈ e.source) :
      U x * ∑ i, fderiv ℝ (V i) x (EuclideanSpace.basisFun (Fin n) ℝ i) =
        u (e x) * D.laplacian v (e x) * g.pullbackVolumeDensity e x := by
    rw [show U x = u (e x) from chartPullback_apply e u hx,
      ← D.density_mul_laplacian_eq_coordinate_divergence e he hei hx (hv (e x))]
    ring
  have hright (x) (hx : x ∈ e.source) :
      (∑ i, fderiv ℝ U x (EuclideanSpace.basisFun (Fin n) ℝ i) * V i x) =
        g.inner (e x) (D.gradient u (e x)) (D.gradient v (e x)) *
          g.pullbackVolumeDensity e x := by
    have hd (w : TangentSpace (𝓡 n) x) : fderiv ℝ U x w =
        mvfderiv (𝓡 n) u (e x) (mfderiv (𝓡 n) (𝓡 n) e x w) := by
      rw [(chartPullback_eventuallyEq e u hx).fderiv_eq]
      have hh := mvfderiv_comp x ((hu (e x)).mdifferentiableAt (by simp))
        (hD.mdifferentiableAt hx)
      have hh' := congrArg (fun L => L w) hh
      simp only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] at hh'
      exact hh'
    calc
      _ = fderiv ℝ U x (mpullback (𝓡 n) (𝓡 n) e (D.gradient v) x) *
          g.pullbackVolumeDensity e x := by
        rw [apply_eq_sum_coordinates, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [V]
        ring
      _ = _ := by
        rw [hd, mpullback,
          (hinv x hx).self_apply_inverse, D.inner_gradient]
  have hlzero (x) (hx : x ∉ e.source) :
      U x * ∑ i, fderiv ℝ (V i) x (EuclideanSpace.basisFun (Fin n) ℝ i) = 0 := by
    simp [U, chartPullback, indicator_of_notMem hx]
  have hrzero (x) (hx : x ∉ e.source) :
      (∑ i, fderiv ℝ U x (EuclideanSpace.basisFun (Fin n) ℝ i) * V i x) = 0 := by
    have hxU : x ∉ tsupport U := fun h => hx (hUs h)
    have hd : fderiv ℝ U x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hxU (tsupport_fderiv_subset ℝ h))
    simp [hd]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hlzero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hrzero] at hparts
  convert hparts using 1
  · exact setIntegral_congr_fun e.open_source.measurableSet (fun x hx => (hleft x hx).symm)
  · congr 1
    exact setIntegral_congr_fun e.open_source.measurableSet (fun x hx => (hright x hx).symm)

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]



theorem integral_mul_laplacian_of_tsupport_subset_chart
    (D : LeviCivitaData g)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ e.target) :
    (∫ x, u x * D.laplacian v x ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient u x) (D.gradient v x) ∂g.volumeMeasure) := by
  have hl : (∫ x in e.target, u x * D.laplacian v x ∂g.volumeMeasure) =
      ∫ x, u x * D.laplacian v x ∂g.volumeMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), zero_mul]
  have hr : (∫ x in e.target, g.inner x (D.gradient u x) (D.gradient v x) ∂g.volumeMeasure) =
      ∫ x, g.inner x (D.gradient u x) (D.gradient v x) ∂g.volumeMeasure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [D.gradient_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), map_zero]
      rfl
  rw [← hl, ← hr,
    g.integral_target_eq_integral_pullback_density e he hei
      (f := fun x => u x * D.laplacian v x)
      (hu.continuous.mul (D.continuous_laplacian hv)).continuousOn,
    g.integral_target_eq_integral_pullback_density e he hei
      (D.continuous_inner_gradient hu hv).continuousOn]
  exact D.integral_mul_laplacian_chart_density e he hei hu hv hc hs

end PoincareConjecture.LeviCivitaData
