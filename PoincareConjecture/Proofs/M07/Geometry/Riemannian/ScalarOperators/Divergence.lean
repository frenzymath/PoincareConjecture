import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Density
import PoincareConjecture.Proofs.M07.Analysis.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Trace

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem laplacian_eq_trace_connection_gradient (D : LeviCivitaData g)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) :
    D.laplacian f x =
      LinearMap.trace ℝ (TangentSpace (𝓡 n) x)
        (D.connection (D.gradient f) x).toLinearMap := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [D.laplacian_eq_sum_inner_connection_gradient hf,
    LinearMap.trace_eq_sum_inner _ (g.orthonormalBasis x)]
  apply Finset.sum_congr rfl
  intro i _
  exact g.symm x _ _

theorem laplacian_eq_sum_basis_connection_gradient (D : LeviCivitaData g)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    D.laplacian f x = ∑ i, b.repr (D.connection (D.gradient f) x (b i)) i := by
  rw [D.laplacian_eq_trace_connection_gradient hf,
    LinearMap.trace_eq_matrix_trace ℝ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    ContinuousLinearMap.coe_coe]

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

set_option backward.isDefEq.respectTransparency false

private noncomputable def metricMatrix
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => g.inner x (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)

private noncomputable def connectionMatrix (D : LeviCivitaData g)
    (x v : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (D.euclideanConnection
    (EuclideanSpace.basisFun (Fin n) ℝ j) v x) i

private theorem fderiv_inner_const_eq (D : LeviCivitaData g)
    (x v a b : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => g.inner y a b) x v =
      g.inner x (D.euclideanConnection a v x) b +
        g.inner x a (D.euclideanConnection b v x) := by
  have h1 := D.inner_connection_const x a v b
  have h2 := D.inner_connection_const x b v a
  have hab : (fun y => g.inner y a b) = (fun y => g.inner y b a) :=
    funext (fun y => g.symm y a b)
  have hav : (fun y => g.inner y a v) = (fun y => g.inner y v a) :=
    funext (fun y => g.symm y a v)
  have hbv : (fun y => g.inner y b v) = (fun y => g.inner y v b) :=
    funext (fun y => g.symm y b v)
  change 2 * g.inner x (D.euclideanConnection a v x) b = _ at h1
  change 2 * g.inner x (D.euclideanConnection b v x) a = _ at h2
  simp only [hab, hav, hbv] at h1 h2 ⊢
  rw [g.symm x a]
  linarith

private theorem inner_eq_sum_coordinates_left
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x a b : EuclideanSpace ℝ (Fin n)) :
    g.inner x a b = ∑ k, a k * g.inner x (EuclideanSpace.basisFun (Fin n) ℝ k) b := by
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin n) => g.inner x v b)
    ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr a)
  simpa only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr] using h.symm

private theorem fderiv_metricMatrix (D : LeviCivitaData g)
    (x v : EuclideanSpace ℝ (Fin n)) :
    Matrix.of (fun i j => fderiv ℝ (fun y => metricMatrix g y i j) x v) =
      (connectionMatrix D x v).transpose * metricMatrix g x +
        metricMatrix g x * connectionMatrix D x v := by
  ext i j
  change fderiv ℝ (fun y => g.inner y (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j)) x v = _
  rw [D.fderiv_inner_const_eq, inner_eq_sum_coordinates_left,
    g.symm x (EuclideanSpace.basisFun (Fin n) ℝ i), inner_eq_sum_coordinates_left]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    metricMatrix, connectionMatrix, Matrix.of_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [g.symm x _ (EuclideanSpace.basisFun (Fin n) ℝ i), mul_comm]

private theorem metricMatrix_det_pos
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : 0 < (metricMatrix g x).det := by
  have h := (g.contDiffAt_pullbackVolumeDensity
    (f := id) (x := x) contMDiffAt_id (by simpa using Function.injective_id)).2
  simpa [RiemannianMetric.pullbackVolumeDensity, metricMatrix, mfderiv_id,
    Real.sqrt_pos] using h

private theorem trace_inv_mul_fderiv_metricMatrix (D : LeviCivitaData g)
    (x v : EuclideanSpace ℝ (Fin n)) :
    Matrix.trace ((metricMatrix g x)⁻¹ *
      Matrix.of (fun i j => fderiv ℝ (fun y => metricMatrix g y i j) x v)) =
      2 * ∑ i, (D.euclideanConnection (EuclideanSpace.basisFun (Fin n) ℝ i) v x) i := by
  rw [D.fderiv_metricMatrix, Matrix.mul_add, Matrix.trace_add]
  have hu : IsUnit (metricMatrix g x).det := (metricMatrix_det_pos g x).ne'.isUnit
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
    Matrix.trace_transpose, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]
  simp only [connectionMatrix, Matrix.trace, Matrix.diag, Matrix.of_apply]
  ring

private theorem density_eq_sqrt_det
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
    g.pullbackVolumeDensity id = fun x => Real.sqrt (metricMatrix g x).det := by
  funext x
  simp [RiemannianMetric.pullbackVolumeDensity, metricMatrix, mfderiv_id]

theorem fderiv_density_eq_connection_trace (D : LeviCivitaData g)
    (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (g.pullbackVolumeDensity id) x v =
      g.pullbackVolumeDensity id x *
        ∑ i, (D.euclideanConnection (EuclideanSpace.basisFun (Fin n) ℝ i) v x) i := by
  have hG (i j : Fin n) : DifferentiableAt ℝ
      (fun y => metricMatrix g y i j) x := by
    exact (((g.contDiffAt_euclideanCoefficients x).clm_apply contDiffAt_const).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  rw [density_eq_sqrt_det, Poincare.Matrix.fderiv_sqrt_det hG (metricMatrix_det_pos g x),
    D.trace_inv_mul_fderiv_metricMatrix]
  ring

theorem contDiffAt_gradient_euclidean (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (D.gradient f) x := by
  have h := (Bundle.contMDiffAt_totalSpace.mp
    (D.contMDiffAt_gradient (contMDiffAt_iff_contDiffAt.mpr hf))).2
  exact contMDiffAt_iff_contDiffAt.mp (by simpa using h)

theorem laplacian_eq_sum_fderiv_gradient_add (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) :
    D.laplacian f x =
      ∑ i, (fderiv ℝ (D.gradient f) x (EuclideanSpace.basisFun (Fin n) ℝ i)) i +
        ∑ i, (D.euclideanConnection (EuclideanSpace.basisFun (Fin n) ℝ i)
          (D.gradient f x) x) i := by
  have hfm : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x :=
    contMDiffAt_iff_contDiffAt.mpr hf
  have hgrad : DifferentiableAt ℝ (D.gradient f) x := by
    exact (D.contDiffAt_gradient_euclidean hf).differentiableAt (by simp)
  rw [D.laplacian_eq_sum_basis_connection_gradient hfm
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  change (∑ i, WithLp.ofLp (show EuclideanSpace ℝ (Fin n) from
    D.connection (D.gradient f) x (EuclideanSpace.basisFun (Fin n) ℝ i)) i) = _
  simp_rw [D.connection_eq_fderiv_add hgrad]
  simpa using Finset.sum_add_distrib
    (s := Finset.univ)
    (f := fun i => (fderiv ℝ (D.gradient f) x
      (EuclideanSpace.basisFun (Fin n) ℝ i)) i)
    (g := fun i => (D.euclideanConnection (EuclideanSpace.basisFun (Fin n) ℝ i)
      (D.gradient f x) x) i)

private theorem apply_eq_sum_coordinates
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, L (EuclideanSpace.basisFun (Fin n) ℝ i) * v i := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    mul_comm] using h.symm

theorem density_mul_laplacian_eq_divergence
    (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) :
    g.pullbackVolumeDensity id x * D.laplacian f x =
      ∑ i, fderiv ℝ (fun y => g.pullbackVolumeDensity id y *
        WithLp.ofLp (D.gradient f y) i) x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hrho : DifferentiableAt ℝ (g.pullbackVolumeDensity id) x :=
    (g.contDiffAt_pullbackVolumeDensity (f := id) contMDiffAt_id
      (by simpa using Function.injective_id)).1.differentiableAt (by simp)
  have hgrad := (D.contDiffAt_gradient_euclidean hf).differentiableAt (by simp)
  have hflux (i : Fin n) :
      fderiv ℝ (fun y => g.pullbackVolumeDensity id y * WithLp.ofLp (D.gradient f y) i)
        x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      fderiv ℝ (g.pullbackVolumeDensity id) x (EuclideanSpace.basisFun (Fin n) ℝ i) *
        WithLp.ofLp (D.gradient f x) i + g.pullbackVolumeDensity id x *
          WithLp.ofLp (fderiv ℝ (D.gradient f) x
            (EuclideanSpace.basisFun (Fin n) ℝ i)) i := by
    have hp := (EuclideanSpace.proj i).hasFDerivAt.comp x hgrad.hasFDerivAt
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) (hrho.hasFDerivAt.mul hp).fderiv
    simpa only [Pi.mul_def, Function.comp_def, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, EuclideanSpace.coe_proj,
      mul_comm, add_comm] using! h
  simp_rw [hflux]
  rw [Finset.sum_add_distrib, ← apply_eq_sum_coordinates,
    ← Finset.mul_sum, D.fderiv_density_eq_connection_trace,
    D.laplacian_eq_sum_fderiv_gradient_add hf]
  ring

end PoincareConjecture.LeviCivitaData
