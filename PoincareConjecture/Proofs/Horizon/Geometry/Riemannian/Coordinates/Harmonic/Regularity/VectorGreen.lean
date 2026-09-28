import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem apply_eq_sum_basis
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, L (EuclideanSpace.basisFun (Fin n) ℝ i) * v i := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    mul_comm] using h.symm

theorem trace_connection_eq_sum_fderiv_add (D : LeviCivitaData g)
    {V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hV : DifferentiableAt ℝ V x) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (D.connection V x).toLinearMap =
      ∑ i, (fderiv ℝ V x (EuclideanSpace.basisFun (Fin n) ℝ i)) i +
        ∑ i, (D.euclideanConnection (EuclideanSpace.basisFun (Fin n) ℝ i)
          (V x) x) i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  change (∑ i, WithLp.ofLp (show EuclideanSpace ℝ (Fin n) from
    D.connection V x (EuclideanSpace.basisFun (Fin n) ℝ i)) i) = _
  simp_rw [D.connection_eq_fderiv_add hV]
  simpa using Finset.sum_add_distrib
    (s := Finset.univ)
    (f := fun i => (fderiv ℝ V x (EuclideanSpace.basisFun (Fin n) ℝ i)) i)
    (g := fun i => (D.euclideanConnection (EuclideanSpace.basisFun (Fin n) ℝ i)
      (V x) x) i)

theorem density_mul_trace_connection_eq_divergence (D : LeviCivitaData g)
    {V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hV : DifferentiableAt ℝ V x) :
    g.pullbackVolumeDensity id x *
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (D.connection V x).toLinearMap =
      ∑ i, fderiv ℝ (fun y => g.pullbackVolumeDensity id y * WithLp.ofLp (V y) i)
        x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hrho : DifferentiableAt ℝ (g.pullbackVolumeDensity id) x :=
    (g.contDiffAt_pullbackVolumeDensity (f := id) contMDiffAt_id
      (by simpa using Function.injective_id)).1.differentiableAt (by simp)
  have hflux (i : Fin n) :
      fderiv ℝ (fun y => g.pullbackVolumeDensity id y * WithLp.ofLp (V y) i)
        x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      fderiv ℝ (g.pullbackVolumeDensity id) x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        WithLp.ofLp (V x) i + g.pullbackVolumeDensity id x *
          WithLp.ofLp (fderiv ℝ V x (EuclideanSpace.basisFun (Fin n) ℝ i)) i := by
    have hp := (EuclideanSpace.proj i).hasFDerivAt.comp x hV.hasFDerivAt
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) (hrho.hasFDerivAt.mul hp).fderiv
    simpa only [Pi.mul_def, Function.comp_def, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, EuclideanSpace.coe_proj,
      mul_comm, add_comm] using! h
  simp_rw [hflux]
  rw [Finset.sum_add_distrib, ← apply_eq_sum_basis, ← Finset.mul_sum,
    D.fderiv_density_eq_connection_trace, D.trace_connection_eq_sum_fderiv_add hV]
  ring

theorem integral_mul_trace_connection_density (D : LeviCivitaData g)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 1 V) (hc : HasCompactSupport u) :
    (∫ x, u x * LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (D.connection V x).toLinearMap * g.pullbackVolumeDensity id x) =
      -(∫ x, fderiv ℝ u x (V x) * g.pullbackVolumeDensity id x) := by
  let F : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x => g.pullbackVolumeDensity id x * WithLp.ofLp (V x) i
  have hF (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ContDiffAt ℝ 1 (F i) x := by
    have hrho := (g.contDiffAt_pullbackVolumeDensity (f := id) (x := x) contMDiffAt_id
      (by simpa using Function.injective_id)).1
    have hp := (EuclideanSpace.proj i).contDiff.contDiffAt.comp x hV.contDiffAt
    exact (hrho.of_le (by simp)).mul hp
  have h := Poincare.integral_mul_coordinate_divergence hu hc (fun i x _ => hF i x)
  have hl (x : EuclideanSpace ℝ (Fin n)) :
      u x * ∑ i, fderiv ℝ (F i) x (EuclideanSpace.basisFun (Fin n) ℝ i) =
        u x * LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
          (D.connection V x).toLinearMap * g.pullbackVolumeDensity id x := by
    rw [← D.density_mul_trace_connection_eq_divergence (hV.differentiable one_ne_zero x)]
    ring
  have hr (x : EuclideanSpace ℝ (Fin n)) :
      (∑ i, fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) * F i x) =
        fderiv ℝ u x (V x) * g.pullbackVolumeDensity id x := by
    rw [apply_eq_sum_basis, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [F]
    ring
  simpa only [hl, hr] using h

private theorem integral_retained_eq_density
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, f x ∂g.volumeMeasure) = ∫ x, f x * g.pullbackVolumeDensity id x := by
  have hvol : g.volumeMeasure =
      volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity id x)) := by
    simpa using g.map_restrict_volumeMeasure_symm
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n))) contMDiffOn_id contMDiffOn_id
  have hs (x : EuclideanSpace ℝ (Fin n)) := g.contDiffAt_pullbackVolumeDensity
    (f := id) (x := x) contMDiffAt_id (by simpa using Function.injective_id)
  have hm : Measurable (fun x => ENNReal.ofReal (g.pullbackVolumeDensity id x)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (continuous_iff_continuousAt.mpr (fun x => (hs x).1.continuousAt)).measurable
  rw [hvol, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hs _).2.le, smul_eq_mul, mul_comm]

theorem integral_mul_trace_connection (D : LeviCivitaData g)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hV : ContDiff ℝ 1 V) (hc : HasCompactSupport u) :
    (∫ x, u x * LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (D.connection V x).toLinearMap ∂g.volumeMeasure) =
      -(∫ x, fderiv ℝ u x (V x) ∂g.volumeMeasure) := by
  simp only [integral_retained_eq_density]
  exact D.integral_mul_trace_connection_density hu hV hc

private theorem integral_fderiv_compact_eq_zero
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, fderiv ℝ f x v) = 0 := by
  have hi : Integrable (fun x => fderiv ℝ f x v) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) (g := f) (v := v)
    (by simp) (by simpa using hi)
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const 1) (fun x _ => hf.differentiable one_ne_zero x)
  simpa using h

theorem integral_trace_connection_eq_zero (D : LeviCivitaData g)
    {V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hV : ContDiff ℝ 1 V) (hc : HasCompactSupport V) :
    (∫ x, LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (D.connection V x).toLinearMap ∂g.volumeMeasure) = 0 := by
  let F : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x => g.pullbackVolumeDensity id x * WithLp.ofLp (V x) i
  have hF (i : Fin n) : ContDiff ℝ 1 (F i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hrho := (g.contDiffAt_pullbackVolumeDensity (f := id) (x := x) contMDiffAt_id
      (by simpa using Function.injective_id)).1
    have hp := (EuclideanSpace.proj i).contDiff.contDiffAt.comp x hV.contDiffAt
    exact (hrho.of_le (by simp)).mul hp
  have hFc (i : Fin n) : HasCompactSupport (F i) := by
    apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    by_contra hx'
    exact hx (by simp [F, image_eq_zero_of_notMem_tsupport hx'])
  rw [integral_retained_eq_density]
  simp_rw [mul_comm _ (g.pullbackVolumeDensity id _),
    D.density_mul_trace_connection_eq_divergence (hV.differentiable one_ne_zero _)]
  change (∫ x, ∑ i, fderiv ℝ (F i) x (EuclideanSpace.basisFun (Fin n) ℝ i)) = 0
  rw [integral_finsetSum _ (fun i _ =>
    (((hF i).continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hFc i).fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)))]
  simp_rw [integral_fderiv_compact_eq_zero (hF _) (hFc _)]
  simp

end PoincareConjecture.LeviCivitaData
