import PoincareConjecture.Proofs.M35.Uniqueness.InitialKilling
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem hessian_centered_metric_quadratic
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    {p : StandardCapSpace} {φ : StandardCapSpace → StandardCapSpace}
    (hφ : ContDiffAt ℝ ∞ φ p) (hzero : φ p = 0)
    (hderiv : HasFDerivAt φ (ContinuousLinearMap.id ℝ StandardCapSpace) p)
    (v w : StandardCapSpace) :
    D.hessian (fun y => g.inner p (φ y) (φ y)) p v w = 2 * g.inner p v w := by
  let B := g.euclideanCoefficients p
  let f : StandardCapSpace → ℝ := fun y => B (φ y) (φ y)
  have hf : ContDiffAt ℝ ∞ f p :=
    (contDiffAt_const.clm_apply hφ).clm_apply hφ
  have hpoint (y : StandardCapSpace) (hy : DifferentiableAt ℝ φ y)
      (a : StandardCapSpace) :
      fderiv ℝ f y a = B (fderiv ℝ φ y a) (φ y) + B (φ y) (fderiv ℝ φ y a) := by
    have hh := ((hasFDerivAt_const B y).clm_apply hy.hasFDerivAt).clm_apply hy.hasFDerivAt
    have heq := congrArg (fun L => L a) hh.fderiv
    simpa only [f, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, zero_apply, zero_add, add_zero, add_comm] using heq
  have hfirst : fderiv ℝ f p = 0 := by
    ext a
    rw [hpoint p hderiv.differentiableAt, hzero]
    simp
  have hA := ((hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const w p)
  have hL := ((hasFDerivAt_const B p).clm_apply hA).clm_apply hderiv
  have hR := ((hasFDerivAt_const B p).clm_apply hderiv).clm_apply hA
  have hsum := hL.add hR
  change HasFDerivAt (fun y => B (fderiv ℝ φ y w) (φ y) +
    B (φ y) (fderiv ℝ φ y w)) _ p at hsum
  have heq : (fun y => fderiv ℝ f y w) =ᶠ[𝓝 p]
      (fun y => B (fderiv ℝ φ y w) (φ y) + B (φ y) (fderiv ℝ φ y w)) := by
    filter_upwards [(hφ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)] with y hy
    exact hpoint y (hy.differentiableAt (by simp)) w
  have hsecond : fderiv ℝ (fderiv ℝ f) p v w = 2 * B v w := by
    have heval :=
      ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const w p)
    have hval := congrArg (fun L => L v) heval.fderiv
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add] at hval
    rw [← hval, heq.fderiv_eq, hsum.fderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, hzero, hderiv.fderiv,
      ContinuousLinearMap.id_apply, zero_apply, map_zero, zero_add, add_zero]
    change B w v + B v w = 2 * B v w
    rw [show B w v = B v w from g.symm p w v]
    ring
  change D.hessian f p v w = _
  rw [D.hessian_eq_fderiv_sub_christoffel hf, hfirst, zero_apply, sub_zero, hsecond]
  rfl

theorem laplacian_centered_metric_quadratic
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    {p : StandardCapSpace} {φ : StandardCapSpace → StandardCapSpace}
    (hφ : ContDiffAt ℝ ∞ φ p) (hzero : φ p = 0)
    (hderiv : HasFDerivAt φ (ContinuousLinearMap.id ℝ StandardCapSpace) p) :
    D.laplacian (fun y => g.inner p (φ y) (φ y)) p = 6 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hb (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) p))) :
      g.inner p (g.orthonormalBasis p i) (g.orthonormalBasis p i) = 1 := by
    change inner ℝ (g.orthonormalBasis p i) (g.orthonormalBasis p i) = 1
    rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis p).norm_eq_one, one_pow]
  simp only [LeviCivitaData.laplacian, hessian_centered_metric_quadratic D hφ hzero hderiv, hb]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) p) = 3 := finrank_euclideanSpace_fin
  norm_num [hdim]

end PoincareConjecture.M35.Uniqueness
