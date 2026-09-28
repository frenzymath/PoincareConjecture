import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Cylinder
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.EuclideanModel
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Matrix
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set PoincareConjecture Module
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

namespace PoincareConjecture.RicciFlow.Splitting

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev cylinderModel := (𝓡 2).prod 𝓘(ℝ, ℝ)

private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

private def sphereInclusionDeriv (x : UnitTwoSphere) : TangentSpace (𝓡 2) x →L[ℝ] E3 :=
  mvfderiv (𝓡 2) (Subtype.val : UnitTwoSphere → E3) x

private theorem sphere_tangent_normal_zero (x : UnitTwoSphere)
    (v : TangentSpace (𝓡 2) x) :
    inner ℝ (x : E3) (sphereInclusionDeriv x v) = 0 := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← range_mvfderiv_subtypeVal (n := 2) x]
  exact ⟨v, rfl⟩

private theorem sphere_tangent_normal_injective (x : UnitTwoSphere) :
    Function.Injective (fun v : TangentSpace (𝓡 2) x × ℝ =>
      sphereInclusionDeriv x v.1 + v.2 • (x : E3)) := by
  intro u v huv
  have hx : inner ℝ (x : E3) (x : E3) = 1 := by
    rw [real_inner_self_eq_norm_sq]
    have hn : ‖(x : E3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    rw [hn, one_pow]
  have hline := congrArg (fun z : E3 => inner ℝ (x : E3) z) huv
  simp only [inner_add_right, real_inner_smul_right, sphere_tangent_normal_zero,
    hx, mul_one, zero_add] at hline
  apply Prod.ext
  · apply injective_mvfderiv_subtypeVal_sphere (n := 2) x
    exact add_right_cancel (by simpa only [hline, sphereInclusionDeriv] using huv)
  · exact hline

variable {P : Type*} [TopologicalSpace P]
  [ChartedSpace E3 P] [IsManifold (𝓡 3) ∞ P]

private theorem contMDiff_deriv_apply_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : P → E) (hf : ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ f)
    (X : ∀ p : P, TangentSpace (𝓡 3) p)
    (hX : ContMDiff (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, E3)) ∞
      (fun p => Bundle.TotalSpace.mk' E3 p (X p))) :
    ContMDiff (𝓡 3) 𝓘(ℝ, E) ∞ (fun p => mvfderiv (𝓡 3) f p (X p)) := by
  exact (contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).comp
    ((hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hX)

private def sphereLineFrame
    (e : P ≃ₘ⟮𝓡 3, cylinderModel⟯ (UnitTwoSphere × ℝ)) (p : P) :
    TangentSpace (𝓡 3) p →L[ℝ] E3 :=
  mvfderiv (𝓡 3) (fun z => (e z).1.val) p +
    (mvfderiv (𝓡 3) (fun z => (e z).2) p).smulRight (e p).1.val

omit [IsManifold (𝓡 3) ∞ P] in
private theorem sphereLineFrame_apply
    (e : P ≃ₘ⟮𝓡 3, cylinderModel⟯ (UnitTwoSphere × ℝ))
    (p : P) (v : TangentSpace (𝓡 3) p) :
    sphereLineFrame e p v =
      sphereInclusionDeriv (e p).1
        (mfderiv (𝓡 3) cylinderModel e p v).1 +
          (mfderiv (𝓡 3) cylinderModel e p v).2 • (e p).1.val := by
  have he := e.contMDiff.mdifferentiable (by simp)
  have hfst : MDifferentiable (𝓡 3) (𝓡 2) (fun z => (e z).1) :=
    mdifferentiable_fst.comp he
  have hcoe : MDifferentiable (𝓡 2) (𝓡 3) (Subtype.val : UnitTwoSphere → E3) :=
    (contMDiff_coe_sphere (n := 2) (m := ∞)).mdifferentiable (by simp)
  unfold sphereLineFrame
  change mvfderiv (𝓡 3)
    ((Subtype.val : UnitTwoSphere → E3) ∘ (Prod.fst ∘ e)) p v +
    mvfderiv (𝓡 3) (Prod.snd ∘ e) p v • (e p).1.val = _
  unfold mvfderiv
  erw [mfderiv_comp p (hcoe _) (hfst p),
    mfderiv_comp p mdifferentiableAt_fst (he p),
    mfderiv_comp p mdifferentiableAt_snd (he p), mfderiv_fst, mfderiv_snd]
  rfl

omit [IsManifold (𝓡 3) ∞ P] in
private theorem sphereLineFrame_bijective
    (e : P ≃ₘ⟮𝓡 3, cylinderModel⟯ (UnitTwoSphere × ℝ)) (p : P) :
    Function.Bijective (sphereLineFrame e p) := by
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) p) := by
    unfold TangentSpace
    infer_instance
  have hi : Function.Injective (sphereLineFrame e p) := by
    intro u v huv
    rw [sphereLineFrame_apply, sphereLineFrame_apply] at huv
    have h := sphere_tangent_normal_injective (e p).1 huv
    exact (e.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) p).injective h
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) p) = Module.finrank ℝ E3 := rfl
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

def sphereLineSmoothOrientation
    (e : P ≃ₘ⟮𝓡 3, cylinderModel⟯ (UnitTwoSphere × ℝ)) :
    SmoothOrientation3 (P := P) where
  form p := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det.compLinearMap
    (sphereLineFrame e p).toLinearMap
  nonvanishing p := by
    let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    let A := LinearEquiv.ofBijective (sphereLineFrame e p).toLinearMap
      (sphereLineFrame_bijective e p)
    refine ⟨fun i => A.symm (b i), ?_⟩
    change b.det (fun i => A (A.symm (b i))) ≠ 0
    simpa only [A.apply_symm_apply, b.det_self] using (one_ne_zero : (1 : ℝ) ≠ 0)
  smooth_on X hX := by
    have hs : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => (e p).1.val) :=
      (contMDiff_coe_sphere (n := 2)).comp (contMDiff_fst.comp e.contMDiff)
    have ht : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun p => (e p).2) :=
      contMDiff_snd.comp e.contMDiff
    have hA (i : Fin 3) : ContMDiff (𝓡 3) (𝓡 3) ∞
        (fun p => sphereLineFrame e p (X i p)) :=
      (contMDiff_deriv_apply_field _ hs (X i) (hX i)).add
        ((contMDiff_deriv_apply_field _ ht (X i) (hX i)).smul hs)
    intro p
    simp only [AlternatingMap.compLinearMap_apply, Basis.det_apply]
    apply Poincare.Manifold.contMDiffAt_matrix_det
    intro i j
    have hproj : ContDiff ℝ ∞ (fun v : E3 => v i) := by fun_prop
    have h := hproj.contMDiff.comp (hA j)
    simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
    convert! h.contMDiffAt using 1

def lineProductSmoothOrientation
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]
    (s : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := N)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := N)
    SmoothOrientation3 (P := N × ℝ) := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := N)
  letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := N)
  exact sphereLineSmoothOrientation
    ((RiemannianMetric.lineProductDiffeomorph (n := 2) (M := N)).symm.trans
      (s.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)))

def canonicalSphereLineSmoothOrientation :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    letI := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
    SmoothOrientation3 (P := UnitTwoSphere × ℝ) :=
  lineProductSmoothOrientation (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞)

end PoincareConjecture.RicciFlow.Splitting
