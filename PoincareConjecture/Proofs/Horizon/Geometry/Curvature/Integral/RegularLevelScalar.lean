import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Bound
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Hypersurface
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.HypersurfaceFields
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryRicci
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Pullback

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology InnerProductSpace BigOperators

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

universe u

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem scalarCurvature_eq_of_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hmetric : ∀ y ∈ U, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {x : M} (hx : x ∈ U) :
    D.scalarCurvature x = D'.scalarCurvature (f x) := by
  let e : TangentSpace (𝓡 n) x ≃ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
      (g.mfderiv_bijective_of_pullback_eq h x
        (fun a b => (hmetric x hx a b).symm))
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let e' := e.isometryOfInner (fun a b => (hmetric x hx a b).symm)
  let B : TangentSpace (𝓡 n) (f x) →ₗ[ℝ]
      TangentSpace (𝓡 n) (f x) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => D'.ricci (f x) u v)
      (fun a b c => by
        unfold LeviCivitaData.ricci
        simp_rw [D'.curvatureTensor_add_first]
        rw [Finset.sum_add_distrib])
      (fun c a b => by
        unfold LeviCivitaData.ricci
        simp_rw [D'.curvatureTensor_smul_first]
        rw [← Finset.mul_sum]
        rfl)
      (fun a b c => by
        unfold LeviCivitaData.ricci
        simp_rw [D'.curvatureTensor_add_third]
        rw [Finset.sum_add_distrib])
      (fun c a b => by
        unfold LeviCivitaData.ricci
        simp_rw [D'.curvatureTensor_smul_third]
        rw [← Finset.mul_sum]
        rfl)
  have htrace := bilinear_sum_orthonormalBasis_eq B
    ((g.orthonormalBasis x).map e') (h.orthonormalBasis (f x))
  have hricci (u v : TangentSpace (𝓡 n) x) :
      D.ricci x u v = D'.ricci (f x) (e u) (e v) := by
    simpa only [e, LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe] using
      (D.ricci_eq_of_local_isometry D' hU hf hmetric hx u v)
  change (∑ i, D.ricci x (g.orthonormalBasis x i) (g.orthonormalBasis x i)) =
    ∑ i, D'.ricci (f x) (h.orthonormalBasis (f x) i)
      (h.orthonormalBasis (f x) i)
  have htarget :
      (∑ i, D'.ricci (f x) (h.orthonormalBasis (f x) i)
        (h.orthonormalBasis (f x) i)) =
        ∑ i, D'.ricci (f x) (e (g.orthonormalBasis x i))
          (e (g.orthonormalBasis x i)) := by
    symm
    simpa only [B, LinearMap.mk₂_apply, OrthonormalBasis.map_apply, e',
      LinearEquiv.coe_isometryOfInner] using htrace
  rw [htarget]
  apply Finset.sum_congr rfl
  intro i hi
  exact hricci (g.orthonormalBasis x i) (g.orthonormalBasis x i)

theorem scalarCurvature_eq_of_eventually_local_isometry
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    {x : M} (hx : x ∈ U)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v)) :
    D.scalarCurvature x = D'.scalarCurvature (f x) := by
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp hmetric
  exact D.scalarCurvature_eq_of_local_isometry D'
    (hU.inter hVo) (hf.mono inter_subset_left)
    (fun y hy => hVsub hy.2) ⟨hx, hxV⟩

noncomputable def coordinateGaussTerm {k : ℕ}
    (h : RiemannianMetric k (EuclideanSpace ℝ (Fin k)))
    (x : EuclideanSpace ℝ (Fin k))
    (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) : ℝ :=
  let b := h.orthonormalBasis x
  (∑ i, h.inner x (A (b i)) (b i)) ^ 2 -
    ∑ i, ∑ j, (h.inner x (A (b i)) (b j)) ^ 2

lemma inner_connection_unitNormal_local
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hreg : 0 < g.inner x (D.gradient f x) (D.gradient f x))
    (v w : TangentSpace (𝓡 n) x)
    (hw : g.inner x (D.gradient f x) w = 0) :
    g.inner x (D.connection
      (fun y => (Real.sqrt (g.inner y (D.gradient f y) (D.gradient f y)))⁻¹ •
        D.gradient f y) x v) w =
      D.hessian f x v w / Real.sqrt (g.inner x (D.gradient f x) (D.gradient f x)) := by
  let q := fun y => g.inner y (D.gradient f y) (D.gradient f y)
  let a := fun y => (Real.sqrt (q y))⁻¹
  letI : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hq : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ q x := by
    have hi := ((g.contMDiff x).clm_bundle_apply
      (D.contMDiffAt_gradient hf)).clm_bundle_apply (D.contMDiffAt_gradient hf)
    simpa [q] using (Bundle.contMDiffAt_totalSpace.mp hi).2
  have ha : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) a x := by
    exact (((Real.contDiffAt_sqrt (show q x ≠ 0 by
      exact ne_of_gt hreg)).contMDiffAt.comp x hq).inv₀
        (Real.sqrt_pos.2 hreg).ne').mdifferentiableAt (by simp)
  have hg := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  change g.inner x (D.connection (a • D.gradient f) x v) w = _
  rw [D.connection.isCovariantDerivativeOn.leibniz hg ha]
  simp only [ContinuousLinearMap.smulRight_apply, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul, hw, mul_zero, add_zero]
  rw [D.hessian_eq_inner_connection_gradient hf]
  simp only [a, q, div_eq_mul_inv, mul_comm]

end PoincareConjecture.LeviCivitaData

namespace Poincare.Geometry.Curvature.Hypersurface

open PoincareConjecture
open PoincareConjecture.LeviCivitaData
open scoped Manifold ContDiff Bundle Topology InnerProductSpace BigOperators

private abbrev ELocal (k : ℕ) := EuclideanSpace ℝ (Fin k)

variable {mLocal : ℕ}
  {gLocal : RiemannianMetric (mLocal + 2) (ELocal (mLocal + 2))}
  {hLocal : RiemannianMetric (mLocal + 1) (ELocal (mLocal + 1))}

private theorem exists_orthonormalBasis_adjoin_early
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (L : V →ₗ[ℝ] W) (hL : ∀ u v, ⟪L u, L v⟫_ℝ = ⟪u, v⟫_ℝ)
    (N : W) (hN : ⟪N, N⟫_ℝ = 1) (hNT : ∀ u, ⟪N, L u⟫_ℝ = 0)
    (hdim : Module.finrank ℝ W = Fintype.card ι + 1) :
    ∃ B : OrthonormalBasis (Option ι) ℝ W,
      B none = N ∧ ∀ i, B (some i) = L (b i) := by
  classical
  let v : Option ι → W := fun i => i.elim N (fun j => L (b j))
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact hN
      | some j => exact hNT (b j)
    | some i =>
      cases j with
      | none => exact (real_inner_comm _ _).trans (hNT (b i))
      | some j => simpa only [v, Option.elim_some, hL, Option.some.injEq]
          using b.inner_eq_ite i j
  have hcard : Fintype.card (Option ι) = Module.finrank ℝ W := by
    simpa using hdim.symm
  let a := basisOfOrthonormalOfCardEqFinrank hv hcard
  have ha : Orthonormal ℝ a := by simpa [a] using hv
  refine ⟨a.toOrthonormalBasis ha, ?_, ?_⟩ <;> simp [a, v]

private theorem inner_shapeOperator_eq_neg_levelHessian_local
    (D : LeviCivitaData gLocal) (D' : LeviCivitaData hLocal)
    {F : ELocal (mLocal + 1) → ELocal (mLocal + 2)}
    {q : ELocal (mLocal + 2) → ℝ} {y : ELocal (mLocal + 1)}
    (hF : ContDiffAt ℝ ∞ F y)
    (hq : ContMDiffAt (𝓡 (mLocal + 2)) 𝓘(ℝ, ℝ) ∞ q (F y))
    (hreg : 0 < gLocal.inner (F y) (D.gradient q (F y))
      (D.gradient q (F y)))
    (N : ELocal (mLocal + 2))
    (hN : N = D.levelUnitNormal q (F y))
    (hNT : ∀ v, gLocal.inner (F y) N (fderiv ℝ F y v) = 0)
    (hNnormal : ∀ᶠ z in 𝓝 y, ∀ w,
      gLocal.inner (F z) (D.levelUnitNormal q (F z)) (fderiv ℝ F z w) = 0)
    (u v : ELocal (mLocal + 1)) :
    hLocal.inner y (shapeOperator D D' F y N u) v =
      -D.hessian q (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) /
        Real.sqrt (D.levelQ q (F y)) := by
  have hNambient : DifferentiableAt ℝ (D.levelUnitNormal q) (F y) := by
    letI : Bundle.RiemannianBundle
        (TangentSpace (𝓡 (mLocal + 2)) : ELocal (mLocal + 2) → Type _) :=
      ⟨gLocal.toRiemannianMetric⟩
    have hq' : ContMDiffAt (𝓡 (mLocal + 2)) 𝓘(ℝ, ℝ) ∞
        (D.levelQ q) (F y) := by
      have hi := ((gLocal.contMDiff (F y)).clm_bundle_apply
        (D.contMDiffAt_gradient hq)).clm_bundle_apply (D.contMDiffAt_gradient hq)
      change ContMDiffAt (𝓡 (mLocal + 2)) 𝓘(ℝ, ℝ) ∞
        (fun z => gLocal.inner z (D.gradient q z) (D.gradient q z)) (F y)
      exact (Bundle.contMDiffAt_totalSpace.mp hi).2
    have hs : ContMDiffAt (𝓡 (mLocal + 2)) 𝓘(ℝ, ℝ) ∞
        (fun z => (Real.sqrt (D.levelQ q z))⁻¹) (F y) := by
      exact ((Real.contDiffAt_sqrt (show D.levelQ q (F y) ≠ 0 by
        exact ne_of_gt hreg)).contMDiffAt.comp (F y) hq').inv₀
        (Real.sqrt_pos.2 hreg).ne'
    have hg := D.contMDiffAt_gradient hq
    have hg' : ContDiffAt ℝ ∞ (D.gradient q) (F y) := by
      exact contMDiffAt_iff_contDiffAt.mp (by simpa using
        (Bundle.contMDiffAt_totalSpace.mp hg).2)
    have hs' : ContDiffAt ℝ ∞
        (fun z => (Real.sqrt (D.levelQ q z))⁻¹) (F y) :=
      contMDiffAt_iff_contDiffAt.mp hs
    have hn' : ContDiffAt ℝ ∞ (D.levelUnitNormal q) (F y) := by
      unfold levelUnitNormal
      exact hs'.smul hg'
    exact hn'.differentiableAt (by simp)
  let Nf : ELocal (mLocal + 1) → ELocal (mLocal + 2) :=
    fun z => D.levelUnitNormal q (F z)
  have hNf : DifferentiableAt ℝ Nf y :=
    hNambient.comp y (hF.differentiableAt (by simp))
  have hNf_eq : Nf y = N := by simpa [Nf] using hN.symm
  have hshape := inner_shapeOperator_neg_normal_eq_normal_derivative
    D D' hF hNf (by simpa [Nf] using hNnormal) u v
  rw [hNf_eq] at hshape
  have hcomp := congrArg (fun L => L u)
    (fderiv_comp y hNambient (hF.differentiableAt (by simp)))
  change fderiv ℝ Nf y u = _ at hcomp
  have hderiv :
      covariantDerivativeAlongMap D F Nf y u =
        D.connection (D.levelUnitNormal q) (F y) (fderiv ℝ F y u) := by
    unfold covariantDerivativeAlongMap
    rw [hcomp, D.connection_eq_fderiv_add hNambient (fderiv ℝ F y u)]
    rfl
  have hshapeNeg : hLocal.inner y (shapeOperator D D' F y (-N) u) v =
      -hLocal.inner y (shapeOperator D D' F y N u) v := by
    rw [inner_shapeOperator, inner_shapeOperator]
    simp only [map_neg, neg_apply]
  have hshapeConn : -hLocal.inner y (shapeOperator D D' F y N u) v =
      gLocal.inner (F y) (D.connection (D.levelUnitNormal q) (F y)
        (fderiv ℝ F y u)) (fderiv ℝ F y v) := by
    calc
      _ = hLocal.inner y (shapeOperator D D' F y (-N) u) v := by rw [hshapeNeg]
      _ = gLocal.inner (F y) (covariantDerivativeAlongMap D F Nf y u)
          (fderiv ℝ F y v) := hshape
      _ = _ := by rw [hderiv]
  have hnormal := PoincareConjecture.LeviCivitaData.inner_connection_unitNormal_local D hq
    hreg (show TangentSpace (𝓡 (mLocal + 2)) (F y) from fderiv ℝ F y u)
      (show TangentSpace (𝓡 (mLocal + 2)) (F y) from fderiv ℝ F y v) ?_
  · have hnormal' :
        gLocal.inner (F y) (D.connection (fun z =>
          (Real.sqrt (gLocal.inner z (D.gradient q z) (D.gradient q z)))⁻¹ •
            D.gradient q z) (F y) (fderiv ℝ F y u)) (fderiv ℝ F y v) =
          D.hessian q (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) /
            Real.sqrt (gLocal.inner (F y) (D.gradient q (F y))
              (D.gradient q (F y))) := by
      change gLocal.inner (F y)
          (D.connection (fun z =>
            (Real.sqrt (D.levelQ q z))⁻¹ • D.gradient q z) (F y)
            (fderiv ℝ F y u)) (fderiv ℝ F y v) = _ at hnormal
      simpa only [levelQ] using hnormal
    have hshapeConn' := hshapeConn
    change -hLocal.inner y (shapeOperator D D' F y N u) v =
      gLocal.inner (F y) (D.connection (fun z =>
        (Real.sqrt (gLocal.inner z (D.gradient q z) (D.gradient q z)))⁻¹ •
        D.gradient q z) (F y) (fderiv ℝ F y u)) (fderiv ℝ F y v) at hshapeConn'
    simp only [levelQ] at ⊢
    calc
      hLocal.inner y (shapeOperator D D' F y N u) v =
          -(-hLocal.inner y (shapeOperator D D' F y N u) v) := by ring
      _ = -gLocal.inner (F y) (D.connection (fun z =>
          (Real.sqrt (gLocal.inner z (D.gradient q z) (D.gradient q z)))⁻¹ •
            D.gradient q z) (F y) (fderiv ℝ F y u)) (fderiv ℝ F y v) := by
        rw [hshapeConn']
      _ = -D.hessian q (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) /
          Real.sqrt (gLocal.inner (F y) (D.gradient q (F y))
            (D.gradient q (F y))) := by rw [hnormal']; ring
  change gLocal.inner (F y) (D.gradient q (F y)) (fderiv ℝ F y v) = 0
  rw [hN, levelUnitNormal] at hNT
  simp only [map_smul, smul_apply, smul_eq_mul] at hNT
  exact (mul_eq_zero.mp (hNT v)).resolve_left
    (by exact inv_ne_zero (Real.sqrt_pos.2 hreg).ne')

end Poincare.Geometry.Curvature.Hypersurface

namespace PoincareConjecture.LeviCivitaData

variable {m : ℕ} {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) P]
  [IsManifold (𝓡 (m + 2)) ∞ P]

def regularLevelNormalShapeOperator
    {g : RiemannianMetric (m + 2) P} (D : LeviCivitaData g)
    {f : P → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    (U : TopologicalSpace.Opens P)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (c : ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg (m + 1) c
    letI := isManifold_openLevelSet hf U hreg (m + 1) c
    (z : openLevelSet f U c) →
      TangentSpace (𝓡 (m + 1)) z →ₗ[ℝ] TangentSpace (𝓡 (m + 1)) z := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openLevelSetChartedSpace hf U hreg (m + 1) c
  letI := isManifold_openLevelSet hf U hreg (m + 1) c
  intro z
  exact Poincare.Geometry.Curvature.Hypersurface.normalShapeOperator
    g (RiemannianMetric.regularLevelMetric hf U hreg c g)
    (contMDiff_openLevelIncl hf U hreg (m + 1) c) z
    (Filter.Eventually.of_forall (RiemannianMetric.regularLevelMetric_inner hf U hreg c g))
    (D.levelUnitNormal f (openLevelIncl f U c z))

private theorem regularLevel_scalarCurvature_gauss_and_shape
    (g : RiemannianMetric (m + 2) P)
    (D : LeviCivitaData g)
    {f : P → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    (U : TopologicalSpace.Opens P)
    (hreg : ∀ x ∈ U,
      mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (c : ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg (m + 1) c
    letI := isManifold_openLevelSet hf U hreg (m + 1) c
    ∀ (D' : LeviCivitaData (RiemannianMetric.regularLevelMetric
      hf U hreg c g)) (z : openLevelSet f U c),
      D'.scalarCurvature z =
        D.scalarCurvature (openLevelIncl f U c z) -
          2 * D.ricci (openLevelIncl f U c z)
            (D.levelUnitNormal f (openLevelIncl f U c z))
            (D.levelUnitNormal f (openLevelIncl f U c z)) +
          D.levelGaussTerm f (openLevelIncl f U c z) ∧
      ∀ u v : TangentSpace (𝓡 (m + 1)) z,
        (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z
          (D.regularLevelNormalShapeOperator hf U hreg c z u) v =
        D.hessian f (openLevelIncl f U c z)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z u)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z v) /
          Real.sqrt (D.levelQ f (openLevelIncl f U c z)) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openLevelSetChartedSpace hf U hreg (m + 1) c
  letI := isManifold_openLevelSet hf U hreg (m + 1) c
  letI : Bundle.RiemannianBundle
      (TangentSpace (𝓡 (m + 2)) : P → Type _) := ⟨g.toRiemannianMetric⟩
  intro D' z
  let x := openLevelIncl f U c z
  have hdf : mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0 := by
    exact hreg x (z.1 : U).property
  have hgrad : D.gradient f x ≠ 0 := by
    intro hz
    exact hdf ((g.gradient_eq_zero_iff_mfderiv_eq_zero f x).mp hz)
  have hQ : 0 < D.levelQ f x := by
    unfold levelQ
    exact real_inner_self_pos.mpr hgrad
  have hN : g.inner x (D.levelUnitNormal f x) (D.levelUnitNormal f x) = 1 := by
    let r := Real.sqrt (D.levelQ f x)
    have hr : 0 < r := Real.sqrt_pos.2 hQ
    have hrq : r ^ 2 = D.levelQ f x := Real.sq_sqrt hQ.le
    rw [levelUnitNormal]
    simp only [map_smul, smul_apply, smul_eq_mul]
    change r⁻¹ * (r⁻¹ * D.levelQ f x) = 1
    rw [← hrq]
    field_simp
  have hnormal : ∀ w : TangentSpace (𝓡 (m + 1)) z,
      g.inner x (D.levelUnitNormal f x)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z w) = 0 := by
    intro w
    have hrange := range_mfderiv_openLevelIncl hf U hreg (m + 1) c z
    have hw : mfderiv (𝓡 (m + 1)) (𝓡 (m + 2))
        (openLevelIncl f U c) z w ∈
        (mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x).ker := by
      rw [← hrange]
      exact ⟨w, rfl⟩
    have hw' := hw
    change mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z w) = 0 at hw'
    have hi : g.inner x (D.gradient f x)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z w) = 0 := by
      rw [D.inner_gradient]
      have hw'' := congrArg (fun q => NormedSpace.fromTangentSpace (f x) q) hw'
      convert hw'' using 1 <;>
        simp only [mvfderiv, ContinuousLinearMap.coe_comp', Function.comp_apply,
          map_zero] <;> rfl
    rw [levelUnitNormal]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [hi, mul_zero]
  let hm : ∀ᶠ p in 𝓝 z, ∀ a b,
      (RiemannianMetric.regularLevelMetric hf U hreg c g).inner p a b =
        g.inner (openLevelIncl f U c p)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) p a)
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) p b) :=
    Filter.Eventually.of_forall (RiemannianMetric.regularLevelMetric_inner
      hf U hreg c g)
  let R := Poincare.Geometry.Curvature.Hypersurface.inducedChartRealization
    g (RiemannianMetric.regularLevelMetric hf U hreg c g)
    (contMDiff_openLevelIncl hf U hreg (m + 1) c) z hm
  let y := extChartAt (𝓡 (m + 1)) z z
  let F := Poincare.Geometry.Curvature.Hypersurface.immersionInCharts
    (m := m + 1) (n := m + 2) (openLevelIncl f U c) z
  let N := D.levelUnitNormal f x
  let Ncoord := mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
    (extChartAt (𝓡 (m + 2)) x) x N
  have hNcoord : R.gE.inner (F y) Ncoord Ncoord = 1 := by
    simpa [R, F, y, N, Ncoord, x] using
      (Poincare.Geometry.Curvature.Hypersurface.chart_normal_coordinate_unit
        g (RiemannianMetric.regularLevelMetric hf U hreg c g)
        (contMDiff_openLevelIncl hf U hreg (m + 1) c) z hm N hN)
  have hNTcoord : ∀ a,
      R.gE.inner (F y) Ncoord (fderiv ℝ F y a) = 0 := by
    exact Poincare.Geometry.Curvature.Hypersurface.chart_normal_coordinate_orthogonal
      g (RiemannianMetric.regularLevelMetric hf U hreg c g)
      (contMDiff_openLevelIncl hf U hreg (m + 1) c) z hm N hnormal
  have hF := Poincare.Geometry.Curvature.Hypersurface.immersionInCharts_eventually_contDiffAt
    (contMDiff_openLevelIncl hf U hreg (m + 1) c) z
  have hcoord :=
    Poincare.Geometry.Curvature.Hypersurface.gauss_scalarCurvature_of_eventually
      R.D R.D' hF R.immersion_metric Ncoord hNcoord hNTcoord
  have hsource := R.D'.scalarCurvature_eq_of_eventually_local_isometry D'
    (isOpen_extChartAt_target z) (contMDiffOn_extChartAt_symm z)
    (mem_extChartAt_target z) R.source_metric
  have hambient := R.D.scalarCurvature_eq_of_eventually_local_isometry D
    (isOpen_extChartAt_target x) (contMDiffOn_extChartAt_symm x)
    (mem_extChartAt_target x) R.ambient_metric
  have hricci := R.D.ricci_eq_of_eventually_local_isometry D
    (isOpen_extChartAt_target x) (contMDiffOn_extChartAt_symm x)
    (mem_extChartAt_target x) R.ambient_metric Ncoord Ncoord
  have hp : (extChartAt (𝓡 (m + 1)) z).symm y = z :=
    (extChartAt (𝓡 (m + 1)) z).left_inv (mem_extChartAt_source z)
  have hq : (extChartAt (𝓡 (m + 2)) x).symm
      (extChartAt (𝓡 (m + 2)) x x) = x :=
    (extChartAt (𝓡 (m + 2)) x).left_inv (mem_extChartAt_source x)
  have hFy : F y = extChartAt (𝓡 (m + 2)) x x := by
    change extChartAt (𝓡 (m + 2)) x
      (openLevelIncl f U c ((extChartAt (𝓡 (m + 1)) z).symm y)) = _
    rw [hp]
  let d := extChartAt (𝓡 (m + 2)) x
  let c0 := extChartAt (𝓡 (m + 1)) z
  let qcoord : EuclideanSpace ℝ (Fin (m + 2)) → ℝ := f ∘ d.symm
  have hfc : ∀ᶠ p in 𝓝 y,
      openLevelIncl f U c (c0.symm p) ∈ d.source := by
    have hc0 : ContMDiffAt (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ c0.symm y := by
      exact (contMDiffWithinAt_extChartAt_symm_target (n := ∞) z
        (mem_extChartAt_target z)).contMDiffAt
        (extChartAt_target_mem_nhds' (mem_extChartAt_target z))
    have hp0 : c0.symm y = z := by simpa [c0] using hp
    have hx : openLevelIncl f U c (c0.symm y) = x := by
      rw [hp0]
    have hs := (isOpen_extChartAt_source (I := 𝓡 (m + 2)) x).mem_nhds
      (mem_extChartAt_source x)
    change (openLevelIncl f U c ∘ c0.symm) ⁻¹' d.source ∈ 𝓝 y
    have hcont := (contMDiff_openLevelIncl hf U hreg (m + 1) c).continuous.continuousAt
      |>.comp hc0.continuousAt
    have hs' : d.source ∈ 𝓝 (openLevelIncl f U c (c0.symm y)) := by
      simpa [d, hx] using hs
    simpa [Function.comp_def] using hcont.preimage_mem_nhds hs'
  have hcomm : (d.symm ∘ F) =ᶠ[𝓝 y]
      (openLevelIncl f U c ∘ c0.symm) := by
    filter_upwards [hfc] with p hp
    unfold F Poincare.Geometry.Curvature.Hypersurface.immersionInCharts d c0
    exact (extChartAt (𝓡 (m + 2)) x).left_inv hp
  have htarget : ∀ᶠ p in 𝓝 y, F p ∈ d.target := by
    filter_upwards [hfc] with p hp
    change extChartAt (𝓡 (m + 2)) x
      (openLevelIncl f U c (c0.symm p)) ∈
      (extChartAt (𝓡 (m + 2)) x).target
    exact (extChartAt (𝓡 (m + 2)) x).map_source hp
  have hqcoord : ContMDiffAt (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ qcoord (F y) := by
    have hy : F y ∈ d.target := htarget.self_of_nhds
    simpa [qcoord, d] using
      (contDiffAt_comp_extChartAt_symm hf x hy).contMDiffAt
  have hqF : qcoord ∘ F =ᶠ[𝓝 y] (fun _ => c) := by
    filter_upwards [hcomm] with p hp
    change f ((d.symm ∘ F) p) = c
    rw [hp]
    change f (openLevelIncl f U c ((extChartAt (𝓡 (m + 1)) z).symm p)) = c
    exact ((extChartAt (𝓡 (m + 1)) z).symm p).property
  have hNnormal : ∀ᶠ p in 𝓝 y, ∀ w,
      R.gE.inner (F p) (R.D.levelUnitNormal qcoord (F p))
        (show TangentSpace (𝓡 (m + 2)) (F p) from fderiv ℝ F p w) = 0 := by
    have hboth := hqF.and (htarget.and hF)
    obtain ⟨V, hVsub, hVo, hyV⟩ := mem_nhds_iff.mp hboth
    filter_upwards [hVo.mem_nhds hyV] with p hp
    have hpall := hVsub hp
    intro w
    have heq : qcoord ∘ F =ᶠ[𝓝 p] (fun _ => c) := by
      filter_upwards [hVo.mem_nhds hp] with s hs
      exact (hVsub hs).1
    have hqdiff : ContDiffAt ℝ ∞ qcoord (F p) := by
      simpa [qcoord, d] using contDiffAt_comp_extChartAt_symm hf x hpall.2.1
    have hqmd : MDifferentiableAt (𝓡 (m + 2)) 𝓘(ℝ, ℝ) qcoord (F p) :=
      (contMDiffAt_iff_contDiffAt.mpr hqdiff).mdifferentiableAt (by simp)
    have hFmd : MDifferentiableAt (𝓡 (m + 1)) (𝓡 (m + 2)) F p :=
      mdifferentiableAt_iff_differentiableAt.mpr
        (hpall.2.2.differentiableAt (by simp))
    have hzero : mvfderiv (𝓡 (m + 1)) (qcoord ∘ F) p
        (show TangentSpace (𝓡 (m + 1)) p from w) = 0 := by
      rw [Poincare.mvfderiv_eq_of_eventuallyEq heq]
      rw [mvfderiv_const]
      rfl
    have hchain := mvfderiv_comp_apply p hqmd hFmd w
    rw [hzero] at hchain
    rw [levelUnitNormal]
    simp only [map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt (R.D.levelQ qcoord (F p)))⁻¹ *
      R.gE.inner (F p) (R.D.gradient qcoord (F p))
        (show TangentSpace (𝓡 (m + 2)) (F p) from fderiv ℝ F p w) = 0
    rw [R.D.inner_gradient]
    change (Real.sqrt (R.D.levelQ qcoord (F p)))⁻¹ *
      mvfderiv (𝓡 (m + 2)) qcoord (F p)
        (show TangentSpace (𝓡 (m + 2)) (F p) from fderiv ℝ F p w) = 0
    have hchain' := hchain.symm
    rw [mfderiv_eq_fderiv] at hchain'
    change mvfderiv (𝓡 (m + 2)) qcoord (F p)
      (show TangentSpace (𝓡 (m + 2)) (F p) from fderiv ℝ F p w) = 0 at hchain'
    rw [hchain', mul_zero]
  have hdx : d.symm (F y) = x := by
    rw [hFy]
    exact (extChartAt (𝓡 (m + 2)) x).left_inv (mem_extChartAt_source x)
  have hdcont : ContMDiffAt (𝓡 (m + 2)) (𝓡 (m + 2)) ∞ d.symm (F y) := by
    have hyd : F y ∈ d.target := htarget.self_of_nhds
    exact (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hyd).contMDiffAt
      (extChartAt_target_mem_nhds' hyd)
  have hd : MDifferentiableAt (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) := by
    exact hdcont.mdifferentiableAt (by simp)
  have hdinv : (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y)).IsInvertible := by
    exact Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm
      (p := x) htarget.self_of_nhds
  have hfd : MDifferentiableAt (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f (d.symm (F y)) := by
    rw [hdx]
    exact (hf x).mdifferentiableAt (by simp)
  have hmetriccoord : ∀ a b,
      R.gE.inner (F y) a b =
        g.inner (d.symm (F y))
          (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) a)
          (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) b) := by
    rw [hFy]
    simpa [d, x, hq] using R.ambient_metric.self_of_nhds
  have hgradcoord := R.D.gradient_comp_eq_mpullback D hd hfd hdinv hmetriccoord
  have hBgrad0 :
      mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y)
        (R.D.gradient qcoord (F y)) = D.gradient f (d.symm (F y)) := by
    have hgradcoord' : R.D.gradient qcoord (F y) =
        _root_.VectorField.mpullback (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm
          (D.gradient f) (F y) := by
      simpa [qcoord] using hgradcoord
    rw [hgradcoord']
    simp only [_root_.VectorField.mpullback_apply]
    exact hdinv.self_apply_inverse (D.gradient f (d.symm (F y)))
  have hBgrad :
      mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y)
        (R.D.gradient qcoord (F y)) = D.gradient f x := by
    rw [hdx] at hBgrad0
    exact hBgrad0
  have hqnorm : R.D.levelQ qcoord (F y) = D.levelQ f x := by
    change R.gE.inner (F y) (R.D.gradient qcoord (F y))
      (R.D.gradient qcoord (F y)) = _
    rw [hmetriccoord, hBgrad, hdx]
    rfl
  have hregcoord : 0 < R.gE.inner (F y) (R.D.gradient qcoord (F y))
      (R.D.gradient qcoord (F y)) := by
    change 0 < R.D.levelQ qcoord (F y)
    rw [hqnorm]
    exact hQ
  have hNcoord_back :
      mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) Ncoord = N := by
    rw [hFy]
    simpa [Ncoord, d] using
      (Poincare.Geometry.Curvature.Hypersurface.ambient_chart_deriv_left_inverse x N)
  have hBlevel :
      mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y)
        (R.D.levelUnitNormal qcoord (F y)) =
        (Real.sqrt (D.levelQ f x))⁻¹ • D.gradient f x := by
    unfold levelUnitNormal
    rw [map_smul, hBgrad, ← hqnorm]
  have hNcoord_level_at_chart :
      Ncoord = R.D.levelUnitNormal qcoord (d x) := by
    have hdinv' :
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (d x)).IsInvertible := by
      exact Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm
        (p := x) (mem_extChartAt_target x)
    apply hdinv'.injective
    have hback :
        mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (d x) Ncoord = N := by
      simpa [Ncoord, d] using
        (Poincare.Geometry.Curvature.Hypersurface.ambient_chart_deriv_left_inverse x N)
    have hlevel := hBlevel
    rw [hFy] at hlevel
    rw [hback, hlevel]
    simp [N, levelUnitNormal]
  have hNcoord_level :
      Ncoord = R.D.levelUnitNormal qcoord (F y) := by
    rw [← hFy] at hNcoord_level_at_chart
    exact hNcoord_level_at_chart
  have hinvcoord : ∀ᶠ p in 𝓝 (F y),
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm p).IsInvertible := by
    have ht : d.target ∈ 𝓝 (F y) :=
      extChartAt_target_mem_nhds' htarget.self_of_nhds
    filter_upwards [ht] with p hp
    exact Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm
      (p := x) hp
  let z0 := c0.symm y
  have hp0 : z0 = z := by simpa [z0, c0] using hp
  have hLC (u : EuclideanSpace ℝ (Fin (m + 1))) :
      mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y)
          (fderiv ℝ F y u) =
        mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z0
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c0.symm y u) := by
    have he := hcomm.mfderiv_eq (I := 𝓡 (m + 1)) (I' := 𝓡 (m + 2))
    have hFyF : ContDiffAt ℝ ∞ F y := hF.self_of_nhds
    have hFmd : MDifferentiableAt (𝓡 (m + 1)) (𝓡 (m + 2)) F y :=
      mdifferentiableAt_iff_differentiableAt.mpr
        (hFyF.differentiableAt (by simp))
    have hc0 : ContMDiffAt (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ c0.symm y := by
      exact (contMDiffWithinAt_extChartAt_symm_target (n := ∞) z
        (mem_extChartAt_target z)).contMDiffAt
        (extChartAt_target_mem_nhds' (mem_extChartAt_target z))
    have hc0md := hc0.mdifferentiableAt (by simp)
    rw [mfderiv_comp y hd hFmd, mfderiv_comp y
      ((contMDiff_openLevelIncl hf U hreg (m + 1) c z0).mdifferentiableAt
        (by simp)) hc0md] at he
    have he' := congrArg (fun A => A u) he
    change mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F y u) =
      mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c)
        (c0.symm y) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c0.symm y u) at he'
    rw [mfderiv_eq_fderiv] at he'
    exact he'
  have hhess (u v : EuclideanSpace ℝ (Fin (m + 1))) :
      R.D.hessian qcoord (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) =
        D.hessian f x
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z0
            (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c0.symm y u))
          (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z0
            (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c0.symm y v)) := by
    have hfcoord : ContMDiffAt (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f
        (d.symm (F y)) := by
      rw [hdx]
      exact hf x
    have hambmetric : ∀ᶠ p in 𝓝 (F y), ∀ a b,
        R.gE.inner p a b = g.inner (d.symm p)
          (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm p a)
          (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm p b) := by
      rw [hFy]
      simpa [d] using R.ambient_metric
    have hh := R.D.hessian_comp_of_metric_pullback D hdcont hinvcoord
      hambmetric hfcoord (fderiv ℝ F y u) (fderiv ℝ F y v)
    rw [hLC u, hLC v] at hh
    rw [hdx] at hh
    simpa [qcoord] using hh
  have hshape_hess (u v : EuclideanSpace ℝ (Fin (m + 1))) :
      R.hE.inner y (Poincare.Geometry.Curvature.Hypersurface.shapeOperator
        R.D R.D' F y Ncoord u) v =
        -R.D.hessian qcoord (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) /
          Real.sqrt (R.D.levelQ qcoord (F y)) := by
    exact Poincare.Geometry.Curvature.Hypersurface.inner_shapeOperator_eq_neg_levelHessian_local
      R.D R.D' hF.self_of_nhds hqcoord hregcoord Ncoord hNcoord_level hNTcoord
      hNnormal u v
  letI : Bundle.RiemannianBundle
      (TangentSpace (𝓡 (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)) → Type _) :=
    ⟨R.hE.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle
      (TangentSpace (𝓡 (m + 2)) : P → Type _) := ⟨g.toRiemannianMetric⟩
  let L : TangentSpace (𝓡 (m + 1)) y →ₗ[ℝ]
      TangentSpace (𝓡 (m + 2)) x :=
    (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y)).toLinearMap.comp
      (fderiv ℝ F y).toLinearMap
  have hL (u v : TangentSpace (𝓡 (m + 1)) y) :
      ⟪L u, L v⟫_ℝ = ⟪u, v⟫_ℝ := by
    change g.inner x
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) (fderiv ℝ F y u))
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) (fderiv ℝ F y v)) =
      R.hE.inner y u v
    have hm := hmetriccoord (fderiv ℝ F y u) (fderiv ℝ F y v)
    rw [hdx] at hm
    calc
      _ = R.gE.inner (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) := hm.symm
      _ = R.hE.inner y u v := (R.immersion_metric.self_of_nhds u v).symm
  have hLN (u : TangentSpace (𝓡 (m + 1)) y) :
      ⟪N, L u⟫_ℝ = 0 := by
    change g.inner x N
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) (fderiv ℝ F y u)) = 0
    let Ncoord' : TangentSpace (𝓡 (m + 2)) (F y) := hFy.symm ▸ Ncoord
    have hNcoord_back' :
        mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) Ncoord' = N := by
      simpa [Ncoord'] using hNcoord_back
    have hm := hmetriccoord Ncoord' (fderiv ℝ F y u)
    rw [hdx] at hm
    calc
      _ = g.inner x
          (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) Ncoord')
          (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (F y) (fderiv ℝ F y u)) := by
            rw [hNcoord_back']
      _ = R.gE.inner (F y) Ncoord' (fderiv ℝ F y u) := hm.symm
      _ = 0 := by
        simpa [Ncoord'] using hNTcoord u
  let b := R.hE.orthonormalBasis y
  let e := g.orthonormalBasis x
  have hdimP : Module.finrank ℝ (TangentSpace (𝓡 (m + 2)) x) = m + 2 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2
    simp
  have hdimL : Module.finrank ℝ (TangentSpace (𝓡 (m + 1)) y) = m + 1 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1
    simp
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 (m + 2)) x) =
      Fintype.card (Fin (Module.finrank ℝ (TangentSpace (𝓡 (m + 1)) y))) + 1 := by
    rw [hdimP, hdimL]
    simp
  obtain ⟨B, hB0, hBi⟩ :=
    Poincare.Geometry.Curvature.Hypersurface.exists_orthonormalBasis_adjoin_early
      b L hL N hN hLN hdim
  let A := D.connection (D.gradient f) x
  let As := (Real.sqrt (D.levelQ f x))⁻¹ • A
  have hA (u v : TangentSpace (𝓡 (m + 2)) x) :
      ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ := by
    change g.inner x (A u) v = g.inner x u (A v)
    rw [g.symm x u]
    exact (D.hessian_eq_inner_connection_gradient (hf x) u v).symm.trans
      ((D.hessian_symm hf x u v).trans
        (D.hessian_eq_inner_connection_gradient (hf x) v u))
  have hAs (u v : TangentSpace (𝓡 (m + 2)) x) :
      ⟪As u, v⟫_ℝ = ⟪u, As v⟫_ℝ := by
    change g.inner x ((Real.sqrt (D.levelQ f x))⁻¹ • A u) v =
      g.inner x u ((Real.sqrt (D.levelQ f x))⁻¹ • A v)
    simp only [map_smul, smul_apply, smul_eq_mul]
    have ha : g.inner x (A u) v = g.inner x u (A v) := by
      exact hA u v
    rw [ha]
  have hAs_inner (u v : TangentSpace (𝓡 (m + 2)) x) :
      ⟪As u, v⟫_ℝ = (Real.sqrt (D.levelQ f x))⁻¹ * g.inner x (A u) v := by
    change g.inner x ((Real.sqrt (D.levelQ f x))⁻¹ • A u) v = _
    simp only [As, A, map_smul, smul_apply, smul_eq_mul,
      real_inner_smul_left]
  have hgaussB := Poincare.LinearAlgebra.gauss_term_orthogonal_restriction
    B As hAs N hN
  have hgaussE := Poincare.LinearAlgebra.gauss_term_orthogonal_restriction
    e As hAs N hN
  let traceForm : TangentSpace (𝓡 (m + 2)) x →ₗ[ℝ]
      TangentSpace (𝓡 (m + 2)) x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => ⟪As u, v⟫_ℝ)
      (by intros; simp only [map_add, inner_add_left])
      (by intros; simp only [map_smul, real_inner_smul_left, smul_eq_mul])
      (by intros; exact inner_add_right ..)
      (by intros; exact real_inner_smul_right ..)
  let normForm : TangentSpace (𝓡 (m + 2)) x →ₗ[ℝ]
      TangentSpace (𝓡 (m + 2)) x →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun u v => ⟪As u, As v⟫_ℝ)
      (by intros; simp only [map_add, inner_add_left])
      (by intros; simp only [map_smul, real_inner_smul_left, smul_eq_mul])
      (by intros; simp only [map_add, inner_add_right])
      (by intros; simp only [map_smul, real_inner_smul_right, smul_eq_mul])
  have htrace : (∑ i, ⟪As (B i), B i⟫_ℝ) = ∑ i, ⟪As (e i), e i⟫_ℝ :=
    bilinear_sum_orthonormalBasis_eq traceForm B e
  have hnormtrace : (∑ i, ⟪As (B i), As (B i)⟫_ℝ) =
      ∑ i, ⟪As (e i), As (e i)⟫_ℝ :=
    bilinear_sum_orthonormalBasis_eq normForm B e
  have hsqB : (∑ i, ∑ j, ⟪As (B i), B j⟫_ℝ ^ 2) =
      ∑ i, ⟪As (B i), As (B i)⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [real_inner_comm (B _), pow_two] using
      B.sum_inner_mul_inner (As (B i)) (As (B i))
  have hsqE : (∑ i, ∑ j, ⟪As (e i), e j⟫_ℝ ^ 2) =
      ∑ i, ⟪As (e i), As (e i)⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [real_inner_comm (e _), pow_two] using
      e.sum_inner_mul_inner (As (e i)) (As (e i))
  have hambient_basis :
      (∑ i, ⟪As (B i), B i⟫_ℝ) ^ 2 -
          ∑ i, ∑ j, ⟪As (B i), B j⟫_ℝ ^ 2 =
        (∑ i, ⟪As (e i), e i⟫_ℝ) ^ 2 -
          ∑ i, ∑ j, ⟪As (e i), e j⟫_ℝ ^ 2 := by
    calc
      _ = (∑ i, ⟪As (B i), B i⟫_ℝ) ^ 2 -
          ∑ i, ⟪As (B i), As (B i)⟫_ℝ := by rw [hsqB]
      _ = (∑ i, ⟪As (e i), e i⟫_ℝ) ^ 2 -
          ∑ i, ⟪As (e i), As (e i)⟫_ℝ := by rw [htrace, hnormtrace]
      _ = _ := by rw [← hsqE]
  have hpair (u v : TangentSpace (𝓡 (m + 1)) y) :
      R.hE.inner y (Poincare.Geometry.Curvature.Hypersurface.shapeOperator
        R.D R.D' F y Ncoord u) v = -⟪As (L u), L v⟫_ℝ := by
    have hh := hhess u v
    rw [hshape_hess u v]
    rw [hh]
    rw [← hLC u, ← hLC v]
    rw [hqnorm]
    change -D.hessian f x (L u) (L v) /
      Real.sqrt (D.levelQ f x) = -⟪As (L u), L v⟫_ℝ
    rw [D.hessian_eq_inner_connection_gradient (hf x)]
    rw [hAs_inner]
    simp only [As, A, map_smul, smul_apply, smul_eq_mul, div_eq_mul_inv,
      real_inner_smul_left, real_inner_smul_right]
    ring

  have hcoord_poly : coordinateGaussTerm R.hE y
      (Poincare.Geometry.Curvature.Hypersurface.shapeOperator
        R.D R.D' F y Ncoord) =
      (∑ i, ⟪As (L (b i)), L (b i)⟫_ℝ) ^ 2 -
        ∑ i, ∑ j, (⟪As (L (b i)), L (b j)⟫_ℝ) ^ 2 := by
    simp only [coordinateGaussTerm, b]
    simp_rw [hpair]
    rw [Finset.sum_neg_distrib]
    ring
  have hproj0 :
      B none - (⟪N, B none⟫_ℝ) • N = 0 := by
    rw [hB0]
    have hNN : ⟪N, N⟫_ℝ = (1 : ℝ) := by
      change g.inner x N N = 1
      exact hN
    rw [hNN]
    simp
  have hproji (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 (m + 1)) y))) :
      B (some i) - (⟪N, B (some i)⟫_ℝ) • N = L (b i) := by
    rw [hBi]
    simp [hLN]
  have hrestriction :
      (∑ i, ⟪As (B i - (⟪N, B i⟫_ℝ) • N),
          B i - (⟪N, B i⟫_ℝ) • N⟫_ℝ) ^ 2 -
        ∑ i, ∑ j, (⟪As (B i - (⟪N, B i⟫_ℝ) • N),
          B j - (⟪N, B j⟫_ℝ) • N⟫_ℝ) ^ 2 =
      (∑ i, ⟪As (L (b i)), L (b i)⟫_ℝ) ^ 2 -
        ∑ i, ∑ j, (⟪As (L (b i)), L (b j)⟫_ℝ) ^ 2 := by
    have hproj (i : Option (Fin (Module.finrank ℝ (TangentSpace (𝓡 (m + 1)) y)))) :
        B i - (⟪N, B i⟫_ℝ) • N = match i with
          | none => 0
          | some j => L (b j) := by
      cases i with
      | none => exact hproj0
      | some j => exact hproji j
    simp only [hproj, Fintype.sum_option]
    simp
  have hlevel : D.levelGaussTerm f x =
      (∑ i, ⟪As (e i - (⟪N, e i⟫_ℝ) • N),
          e i - (⟪N, e i⟫_ℝ) • N⟫_ℝ) ^ 2 -
        ∑ i, ∑ j, (⟪As (e i - (⟪N, e i⟫_ℝ) • N),
          e j - (⟪N, e j⟫_ℝ) • N⟫_ℝ) ^ 2 := by
    change (∑ i, D.hessian f x
      (e i - (g.inner x N (e i)) • N)
      (e i - (g.inner x N (e i)) • N) / Real.sqrt (D.levelQ f x)) ^ 2 -
      ∑ i, ∑ j, (D.hessian f x
        (e i - (g.inner x N (e i)) • N)
        (e j - (g.inner x N (e j)) • N) / Real.sqrt (D.levelQ f x)) ^ 2 = _
    have hinner (u v : TangentSpace (𝓡 (m + 2)) x) :
        ⟪u, v⟫_ℝ = g.inner x u v := by
      rfl
    simp_rw [hinner]
    simp_rw [D.hessian_eq_inner_connection_gradient (hf x)]
    simp only [As, A, map_smul, smul_apply, smul_eq_mul, div_eq_mul_inv,
      real_inner_smul_left, real_inner_smul_right]
    ring_nf
    ring
  have hgauss_basis :
      (∑ i, ⟪As (B i), B i⟫_ℝ) ^ 2 -
          ∑ i, ∑ j, ⟪As (B i), B j⟫_ℝ ^ 2 -
          (2 * ∑ i, ⟪As (B i), B i⟫_ℝ) * ⟪As N, N⟫_ℝ +
          2 * ⟪As N, As N⟫_ℝ =
        (∑ i, ⟪As (e i), e i⟫_ℝ) ^ 2 -
          ∑ i, ∑ j, ⟪As (e i), e j⟫_ℝ ^ 2 -
          (2 * ∑ i, ⟪As (e i), e i⟫_ℝ) * ⟪As N, N⟫_ℝ +
          2 * ⟪As N, As N⟫_ℝ := by
    rw [htrace]
    have hb := hambient_basis
    rw [htrace] at hb
    linear_combination hb
  have hcoord_level : coordinateGaussTerm R.hE y
      (Poincare.Geometry.Curvature.Hypersurface.shapeOperator
        R.D R.D' F y Ncoord) = D.levelGaussTerm f x := by
    exact hcoord_poly.trans
      (hrestriction.symm.trans
        ((hgaussB.trans (hgauss_basis.trans hgaussE.symm)).trans hlevel.symm))
  have hNi : mfderiv (𝓡 (m + 2)) (𝓡 (m + 2))
      (extChartAt (𝓡 (m + 2)) x).symm
      (extChartAt (𝓡 (m + 2)) x x) Ncoord = N :=
    Poincare.Geometry.Curvature.Hypersurface.ambient_chart_deriv_left_inverse x N
  rw [hq] at hambient
  rw [hNi, hq] at hricci
  have hcoord_scalar := hcoord
  change R.D'.scalarCurvature y = D'.scalarCurvature
    ((extChartAt (𝓡 (m + 1)) z).symm y) at hsource
  rw [hp] at hsource
  change R.D'.scalarCurvature y = R.D.scalarCurvature (F y) -
    2 * R.D.ricci (F y) Ncoord Ncoord +
    (∑ i, R.hE.inner y
      (Poincare.Geometry.Curvature.Hypersurface.shapeOperator R.D R.D' F y Ncoord
        (R.hE.orthonormalBasis y i)) (R.hE.orthonormalBasis y i)) ^ 2 -
    ∑ i, ∑ j, (R.hE.inner y
      (Poincare.Geometry.Curvature.Hypersurface.shapeOperator R.D R.D' F y Ncoord
        (R.hE.orthonormalBasis y i)) (R.hE.orthonormalBasis y j)) ^ 2 at hcoord_scalar
  rw [hsource, hFy, hambient, hricci] at hcoord_scalar
  rw [add_sub_assoc] at hcoord_scalar
  change D'.scalarCurvature z = D.scalarCurvature x - 2 * D.ricci x N N +
    coordinateGaussTerm R.hE y
      (Poincare.Geometry.Curvature.Hypersurface.shapeOperator R.D R.D' F y Ncoord) at hcoord_scalar
  rw [hcoord_level] at hcoord_scalar
  refine ⟨hcoord_scalar, ?_⟩
  intro u v
  have hsourceId := mfderivWithin_range_extChartAt_symm (I := 𝓡 (m + 1)) (x := z)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hsourceId
  have hsourceId' (w : EuclideanSpace ℝ (Fin (m + 1))) :
      mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c0.symm y w = w :=
    congrArg (fun A => A w) hsourceId
  have hsourceMetric (a b : EuclideanSpace ℝ (Fin (m + 1))) :
      R.hE.inner y a b = (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z a b := by
    have hi := R.source_metric.self_of_nhds a b
    change R.hE.inner y a b =
      (RiemannianMetric.regularLevelMetric hf U hreg c g).inner (c0.symm y)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c0.symm y a)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c0.symm y b) at hi
    rw [hsourceId', hsourceId', hp] at hi
    exact hi
  have hshapeBack : D.regularLevelNormalShapeOperator hf U hreg c z u =
      Poincare.Geometry.Curvature.Hypersurface.shapeOperator R.D R.D' F y (-Ncoord) u := by
    change mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c0.symm y
      (Poincare.Geometry.Curvature.Hypersurface.shapeOperator R.D R.D' F y
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d x (-N))
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c0 z u)) = _
    rw [hsourceId', map_neg]
    have hu := congrArg (fun A => A u)
      (mfderiv_extChartAt_self (I := 𝓡 (m + 1)) (x := z))
    rw [hu]
    rfl
  rw [hshapeBack, ← hsourceMetric]
  have hneg : R.hE.inner y
      (Poincare.Geometry.Curvature.Hypersurface.shapeOperator R.D R.D' F y (-Ncoord) u) v =
      -R.hE.inner y
        (Poincare.Geometry.Curvature.Hypersurface.shapeOperator R.D R.D' F y Ncoord u) v := by
    rw [Poincare.Geometry.Curvature.Hypersurface.inner_shapeOperator,
      Poincare.Geometry.Curvature.Hypersurface.inner_shapeOperator]
    simp only [map_neg, neg_apply]
  rw [hneg, hshape_hess, hhess, hqnorm, hsourceId', hsourceId', hp0]
  ring

theorem regularLevel_scalarCurvature_gauss
    (g : RiemannianMetric (m + 2) P) (D : LeviCivitaData g)
    {f : P → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    (U : TopologicalSpace.Opens P)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (c : ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg (m + 1) c
    letI := isManifold_openLevelSet hf U hreg (m + 1) c
    ∀ (D' : LeviCivitaData (RiemannianMetric.regularLevelMetric hf U hreg c g))
      (z : openLevelSet f U c),
      D'.scalarCurvature z = D.scalarCurvature (openLevelIncl f U c z) -
        2 * D.ricci (openLevelIncl f U c z)
          (D.levelUnitNormal f (openLevelIncl f U c z))
          (D.levelUnitNormal f (openLevelIncl f U c z)) +
        D.levelGaussTerm f (openLevelIncl f U c z) := by
  intro D' z
  exact (D.regularLevel_scalarCurvature_gauss_and_shape g hf U hreg c D' z).1

theorem regularLevelNormalShapeOperator_inner
    {g : RiemannianMetric (m + 2) P} (D : LeviCivitaData g)
    {f : P → ℝ} (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f)
    (U : TopologicalSpace.Opens P)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (c : ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hreg (m + 1) c
    letI := isManifold_openLevelSet hf U hreg (m + 1) c
    ∀ (D' : LeviCivitaData (RiemannianMetric.regularLevelMetric hf U hreg c g))
      (z : openLevelSet f U c) (u v : TangentSpace (𝓡 (m + 1)) z),
      (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z
        (D.regularLevelNormalShapeOperator hf U hreg c z u) v =
      D.hessian f (openLevelIncl f U c z)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) (openLevelIncl f U c) z v) /
        Real.sqrt (D.levelQ f (openLevelIncl f U c z)) := by
  intro D' z u v
  exact (D.regularLevel_scalarCurvature_gauss_and_shape g hf U hreg c D' z).2 u v

lemma inner_connection_unitNormal_of_contMDiffAt
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hreg : 0 < g.inner x (D.gradient f x) (D.gradient f x))
    (v w : TangentSpace (𝓡 n) x)
    (hw : g.inner x (D.gradient f x) w = 0) :
    g.inner x (D.connection
      (fun y => (Real.sqrt (g.inner y (D.gradient f y) (D.gradient f y)))⁻¹ •
        D.gradient f y) x v) w =
      D.hessian f x v w / Real.sqrt (g.inner x (D.gradient f x) (D.gradient f x)) := by
  let q := fun y => g.inner y (D.gradient f y) (D.gradient f y)
  let a := fun y => (Real.sqrt (q y))⁻¹
  letI : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hq : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ q x := by
    have hi := ((g.contMDiff x).clm_bundle_apply
      (D.contMDiffAt_gradient hf)).clm_bundle_apply (D.contMDiffAt_gradient hf)
    simpa [q] using (Bundle.contMDiffAt_totalSpace.mp hi).2
  have ha : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) a x := by
    exact (((Real.contDiffAt_sqrt (show q x ≠ 0 by
      exact ne_of_gt hreg)).contMDiffAt.comp x hq).inv₀
        (Real.sqrt_pos.2 hreg).ne').mdifferentiableAt (by simp)
  have hg := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  change g.inner x (D.connection (a • D.gradient f) x v) w = _
  rw [D.connection.isCovariantDerivativeOn.leibniz hg ha]
  simp only [ContinuousLinearMap.smulRight_apply, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul, hw, mul_zero, add_zero]
  rw [D.hessian_eq_inner_connection_gradient hf]
  simp only [a, q, div_eq_mul_inv, mul_comm]

end PoincareConjecture.LeviCivitaData

namespace Poincare.Geometry.Curvature.Hypersurface

open PoincareConjecture
open PoincareConjecture.LeviCivitaData
open scoped Manifold ContDiff Bundle Topology BigOperators

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

variable {m : ℕ}
  {g : RiemannianMetric (m + 1) (E (m + 1))}
  {h : RiemannianMetric m (E m)}

private theorem exists_orthonormalBasis_adjoin_local
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (L : V →ₗ[ℝ] W) (hL : ∀ u v, ⟪L u, L v⟫_ℝ = ⟪u, v⟫_ℝ)
    (N : W) (hN : ⟪N, N⟫_ℝ = 1) (hNT : ∀ u, ⟪N, L u⟫_ℝ = 0)
    (hdim : Module.finrank ℝ W = Fintype.card ι + 1) :
    ∃ B : OrthonormalBasis (Option ι) ℝ W,
      B none = N ∧ ∀ i, B (some i) = L (b i) := by
  classical
  let v : Option ι → W := fun i => i.elim N (fun j => L (b j))
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact hN
      | some j => exact hNT (b j)
    | some i =>
      cases j with
      | none => exact (real_inner_comm _ _).trans (hNT (b i))
      | some j => simpa only [v, Option.elim_some, hL, Option.some.injEq]
          using b.inner_eq_ite i j
  have hcard : Fintype.card (Option ι) = Module.finrank ℝ W := by
    simpa using hdim.symm
  let a := basisOfOrthonormalOfCardEqFinrank hv hcard
  have ha : Orthonormal ℝ a := by simpa [a] using hv
  refine ⟨a.toOrthonormalBasis ha, ?_, ?_⟩ <;> simp [a, v]

theorem inner_shapeOperator_eq_neg_levelHessian
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E m → E (m + 1)} {q : E (m + 1) → ℝ} {y : E m}
    (hF : ContDiffAt ℝ ∞ F y)
    (hq : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ q (F y))
    (hreg : 0 < g.inner (F y) (D.gradient q (F y)) (D.gradient q (F y)))
    (N : E (m + 1))
    (hN : N = D.levelUnitNormal q (F y))
    (hNT : ∀ v, g.inner (F y) N (fderiv ℝ F y v) = 0)
    (hNnormal : ∀ᶠ z in 𝓝 y, ∀ w,
      g.inner (F z) (D.levelUnitNormal q (F z)) (fderiv ℝ F z w) = 0)
    (u v : E m) :
    h.inner y (shapeOperator D D' F y N u) v =
      -D.hessian q (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) /
        Real.sqrt (D.levelQ q (F y)) := by
  have hNambient : DifferentiableAt ℝ (D.levelUnitNormal q) (F y) := by
    letI : Bundle.RiemannianBundle
        (TangentSpace (𝓡 (m + 1)) : E (m + 1) → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hq' : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞
        (D.levelQ q) (F y) := by
      have hi := ((g.contMDiff (F y)).clm_bundle_apply
        (D.contMDiffAt_gradient hq)).clm_bundle_apply (D.contMDiffAt_gradient hq)
      change ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞
        (fun z => g.inner z (D.gradient q z) (D.gradient q z)) (F y)
      exact (Bundle.contMDiffAt_totalSpace.mp hi).2
    have hs : ContMDiffAt (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞
        (fun z => (Real.sqrt (D.levelQ q z))⁻¹) (F y) := by
      exact ((Real.contDiffAt_sqrt (show D.levelQ q (F y) ≠ 0 by
        exact ne_of_gt hreg)).contMDiffAt.comp (F y) hq').inv₀
        (Real.sqrt_pos.2 hreg).ne'
    have hg := D.contMDiffAt_gradient hq
    have hg' : ContDiffAt ℝ ∞ (D.gradient q) (F y) := by
      exact contMDiffAt_iff_contDiffAt.mp (by simpa using
        (Bundle.contMDiffAt_totalSpace.mp hg).2)
    have hs' : ContDiffAt ℝ ∞
        (fun z => (Real.sqrt (D.levelQ q z))⁻¹) (F y) :=
      contMDiffAt_iff_contDiffAt.mp hs
    have hn' : ContDiffAt ℝ ∞ (D.levelUnitNormal q) (F y) := by
      unfold levelUnitNormal
      exact hs'.smul hg'
    exact hn'.differentiableAt (by simp)
  let Nf : E m → E (m + 1) := fun z => D.levelUnitNormal q (F z)
  have hNf : DifferentiableAt ℝ Nf y := by
    exact hNambient.comp y (hF.differentiableAt (by simp))
  have hNf_eq : Nf y = N := by simpa [Nf] using hN.symm
  have hshape :=
    inner_shapeOperator_neg_normal_eq_normal_derivative
      D D' hF hNf (by simpa [Nf] using hNnormal) u v
  rw [hNf_eq] at hshape
  have hcomp := congrArg (fun L => L u)
    (fderiv_comp y hNambient (hF.differentiableAt (by simp)))
  change fderiv ℝ Nf y u = _ at hcomp
  have hderiv :
      covariantDerivativeAlongMap D F Nf y u =
        D.connection (D.levelUnitNormal q) (F y) (fderiv ℝ F y u) := by
    unfold covariantDerivativeAlongMap
    rw [hcomp, D.connection_eq_fderiv_add hNambient (fderiv ℝ F y u)]
    rfl
  have hshapeNeg : h.inner y (shapeOperator D D' F y (-N) u) v =
      -h.inner y (shapeOperator D D' F y N u) v := by
    rw [inner_shapeOperator, inner_shapeOperator]
    simp only [map_neg, neg_apply]
  have hshapeConn : -h.inner y (shapeOperator D D' F y N u) v =
      g.inner (F y) (D.connection (D.levelUnitNormal q) (F y)
        (fderiv ℝ F y u)) (fderiv ℝ F y v) := by
    calc
      _ = h.inner y (shapeOperator D D' F y (-N) u) v := by rw [hshapeNeg]
      _ = g.inner (F y) (covariantDerivativeAlongMap D F Nf y u)
          (fderiv ℝ F y v) := hshape
      _ = _ := by rw [hderiv]
  have hnormal := PoincareConjecture.LeviCivitaData.inner_connection_unitNormal_of_contMDiffAt D hq
    hreg (show TangentSpace (𝓡 (m + 1)) (F y) from fderiv ℝ F y u)
      (show TangentSpace (𝓡 (m + 1)) (F y) from fderiv ℝ F y v) ?_
  · have hnormal' :
        g.inner (F y) (D.connection (fun z =>
          (Real.sqrt (g.inner z (D.gradient q z) (D.gradient q z)))⁻¹ •
            D.gradient q z) (F y) (fderiv ℝ F y u)) (fderiv ℝ F y v) =
          D.hessian q (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) /
            Real.sqrt (g.inner (F y) (D.gradient q (F y))
              (D.gradient q (F y))) := by
      change g.inner (F y)
          (D.connection (fun z =>
            (Real.sqrt (D.levelQ q z))⁻¹ • D.gradient q z) (F y)
            (fderiv ℝ F y u)) (fderiv ℝ F y v) = _
        at hnormal
      simpa only [levelQ] using hnormal
    have hshapeConn' := hshapeConn
    change -h.inner y (shapeOperator D D' F y N u) v =
      g.inner (F y) (D.connection (fun z =>
        (Real.sqrt (g.inner z (D.gradient q z) (D.gradient q z)))⁻¹ •
        D.gradient q z) (F y) (fderiv ℝ F y u)) (fderiv ℝ F y v) at hshapeConn'
    simp only [levelQ] at ⊢
    calc
      h.inner y (shapeOperator D D' F y N u) v =
          -(-h.inner y (shapeOperator D D' F y N u) v) := by ring
      _ = -g.inner (F y) (D.connection (fun z =>
          (Real.sqrt (g.inner z (D.gradient q z) (D.gradient q z)))⁻¹ •
            D.gradient q z) (F y) (fderiv ℝ F y u)) (fderiv ℝ F y v) := by
        rw [hshapeConn']
      _ = -D.hessian q (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) /
          Real.sqrt (g.inner (F y) (D.gradient q (F y))
            (D.gradient q (F y))) := by rw [hnormal']; ring
  change g.inner (F y) (D.gradient q (F y)) (fderiv ℝ F y v) = 0
  rw [hN, levelUnitNormal] at hNT
  simp only [map_smul, smul_apply, smul_eq_mul] at hNT
  exact (mul_eq_zero.mp (hNT v)).resolve_left
    (by exact inv_ne_zero (Real.sqrt_pos.2 hreg).ne')

end Poincare.Geometry.Curvature.Hypersurface
