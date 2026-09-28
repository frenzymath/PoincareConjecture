import PoincareConjecture.Proofs.M48.HessianTensorial
import PoincareConjecture.Proofs.M48.Trace
import PoincareConjecture.Proofs.M48.RicciNormTransport
import PoincareConjecture.Proofs.M04.ScalarEvolution
import Mathlib.Geometry.Manifold.VectorField.Pullback

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators

universe u v

namespace PoincareConjecture

open M48ScalarCalculus

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}
  {f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞}

theorem MetricHomothetyCalculus.m48_hessian_eq
    (H : MetricHomothetyCalculus g h f 1)
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (phi : N → ℝ) (hphi : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ phi)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D'.hessian phi (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
        (mfderiv (𝓡 n) (𝓡 n) f x v) = D.hessian (phi ∘ f) x u v := by
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n))
    (mfderiv (𝓡 n) (𝓡 n) f x v)
  obtain ⟨V₀, hV₀, hW₀⟩ := FiberBundle.exists_contMDiffOn_extend
    (𝓡 n) (EuclideanSpace ℝ (Fin n)) (k := ∞)
    (mfderiv (𝓡 n) (𝓡 n) f x v)
  obtain ⟨V, hVV₀, hV, hxV⟩ := mem_nhds_iff.mp hV₀
  have hW : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) V :=
    hW₀.mono hVV₀
  let U := f ⁻¹' V
  have hU : IsOpen U := hV.preimage f.continuous
  have hxU : x ∈ U := hxV
  have hfInv (y : M) : (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible :=
    ⟨(f.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
      (x := y) (Set.mem_univ y), rfl⟩
  let Y := VectorField.mpullback (𝓡 n) (𝓡 n) f W
  have hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U :=
    hW.mpullback_vectorField_preimage f.contMDiff (fun y _ => hfInv y) (by simp)
  have hlink (y : M) : W (f y) = mfderiv (𝓡 n) (𝓡 n) f y (Y y) :=
    ((hfInv y).self_apply_inverse (W (f y))).symm
  have hYx : Y x = v := by
    apply (hfInv x).injective
    rw [← hlink]
    exact FiberBundle.extend_apply_self _ _
  have hSource := hessian_eq_fields D (phi ∘ f) x
    (hphi.comp f.contMDiff).contMDiffAt
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u) Y
    (FiberBundle.mdifferentiableAt_extend ..)
    (((hY x hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp))
  simp only [FiberBundle.extend_apply_self, hYx] at hSource
  rw [hSource]
  have hconn := H.connection_eq D D' U hU Y W hY
    (hW.mono (by intro y hy; obtain ⟨z, hz, rfl⟩ := hy; exact hz))
    (fun y _ => hlink y) x hxU u
  have hfunc : (fun y => mvfderiv (𝓡 n) (phi ∘ f) y (Y y)) =
      (fun z => mvfderiv (𝓡 n) phi z (W z)) ∘ f := by
    funext y
    rw [mvfderiv_comp_apply y (hphi.mdifferentiable (by simp) (f y))
      (f.mdifferentiable (by simp) y), ← hlink]
    rfl
  have hPsi := scalar_directional_mdifferentiableAt hphi.contMDiffAt W
    (((hW (f x) hxV).contMDiffAt (hV.mem_nhds hxV)).mdifferentiableAt (by simp))
  simp only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self]
  change mvfderiv (𝓡 n) (fun z => mvfderiv (𝓡 n) phi z (W z)) (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x u) -
      mvfderiv (𝓡 n) phi (f x) (D'.connection W (f x)
        (mfderiv (𝓡 n) (𝓡 n) f x u)) = _
  rw [hfunc, mvfderiv_comp_apply x hPsi (f.mdifferentiable (by simp) x),
    hconn, mvfderiv_comp_apply x (hphi.mdifferentiable (by simp) (f x))
      (f.mdifferentiable (by simp) x)]

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in

theorem LeviCivitaData.m48_laplacian_eq_sum
    (D : LeviCivitaData g) (phi : M → ℝ) (x : M)
    (hphi : ContMDiffAt (𝓡 n) 𝓘(ℝ) ∞ phi x)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0) :
    D.laplacian phi x = ∑ i, D.hessian phi x (b i) (b i) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  have hb' : Orthonormal ℝ b := orthonormal_iff_ite.mpr hb
  simpa only [LeviCivitaData.laplacian, hessianBilin_apply_eq_hessian,
    Module.Basis.coe_toOrthonormalBasis] using
      sum_diag_basis_independent (hessianBilin D phi x hphi)
        (g.orthonormalBasis x) (b.toOrthonormalBasis hb')

theorem MetricHomothetyCalculus.m48_laplacian_eq
    (H : MetricHomothetyCalculus g h f 1) (hf : MetricHomothety g h f 1)
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (phi : N → ℝ) (hphi : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ phi) (x : M) :
    D'.laplacian phi (f x) = D.laplacian (phi ∘ f) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let b := (g.orthonormalBasis x).toBasis
  let e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    ((f.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv
      (x := x) (Set.mem_univ x)).toLinearEquiv
  have he (v : TangentSpace (𝓡 n) x) :
      e v = mfderiv (𝓡 n) (𝓡 n) f x v := rfl
  have hb (i j) : g.inner x (b i) (b j) = if i = j then 1 else 0 := by
    exact (g.orthonormalBasis x).inner_eq_ite i j
  have hc (i j) : h.inner (f x) ((b.map e) i) ((b.map e) j) =
      if i = j then 1 else 0 := by
    rw [Module.Basis.map_apply, Module.Basis.map_apply, he, he, hf]
    simpa using hb i j
  rw [D'.m48_laplacian_eq_sum phi (f x) hphi.contMDiffAt (b.map e) hc]
  simp_rw [Module.Basis.map_apply, he, H.m48_hessian_eq D D' phi hphi]
  rfl

theorem SurgeryRegularSlab.m48_scalarCurvature_eq
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {a b : ℝ}
    (B : SurgeryRegularSlab slice metric a b) (t : Set.Icc a b)
    (D : LeviCivitaData (metric t.1)) (x : (slice a).carrier) :
    D.scalarCurvature (B.identify t x) = (B.flow.connection t.1).scalarCurvature x := by
  have hf : MetricHomothety (B.flow.metric t.1) (metric t.1) (B.identify t) 1 := by
    intro y v w
    simpa only [one_mul] using B.metric_pullback t y v w
  have H := (generalizedParabolicRescaling_from_M12 3).metric_homothety
    (slice a).carrier (slice t.1).carrier (B.flow.metric t.1) (metric t.1)
    (B.identify t) 1 (by norm_num) hf
  simpa only [div_one] using H.scalar_eq (B.flow.connection t.1) D x

theorem SurgeryRegularSlab.m48_scalarLaplacian_eq
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {a b : ℝ}
    (B : SurgeryRegularSlab slice metric a b) (t : Set.Icc a b)
    (D : LeviCivitaData (metric t.1)) (x : (slice a).carrier) :
    D.laplacian D.scalarCurvature (B.identify t x) =
      (B.flow.connection t.1).laplacian (B.flow.connection t.1).scalarCurvature x := by
  have hf : MetricHomothety (B.flow.metric t.1) (metric t.1) (B.identify t) 1 := by
    intro y v w
    simpa only [one_mul] using B.metric_pullback t y v w
  have H := (generalizedParabolicRescaling_from_M12 3).metric_homothety
    (slice a).carrier (slice t.1).carrier (B.flow.metric t.1) (metric t.1)
    (B.identify t) 1 (by norm_num) hf
  have hscalar : D.scalarCurvature ∘ B.identify t =
      (B.flow.connection t.1).scalarCurvature :=
    funext (B.m48_scalarCurvature_eq t D)
  have hinverse : D.scalarCurvature =
      (B.flow.connection t.1).scalarCurvature ∘ (B.identify t).symm := by
    funext y
    simpa only [Diffeomorph.apply_symm_apply, Function.comp_apply] using
      B.m48_scalarCurvature_eq t D ((B.identify t).symm y)
  have hreg : ContMDiff (𝓡 3) 𝓘(ℝ) ∞ D.scalarCurvature := by
    rw [hinverse]
    exact (B.flow.contMDiff_scalarCurvature t.1 t.2).comp (B.identify t).symm.contMDiff
  simpa only [hscalar] using
    H.m48_laplacian_eq hf (B.flow.connection t.1) D D.scalarCurvature hreg x

end PoincareConjecture
