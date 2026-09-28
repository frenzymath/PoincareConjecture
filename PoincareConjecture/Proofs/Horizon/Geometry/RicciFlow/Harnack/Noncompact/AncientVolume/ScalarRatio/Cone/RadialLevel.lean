import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.RegularLevelScalar












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {m n : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) L]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 m) ∞ L] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local instance tangent_finiteDimensional (x : L) :
    FiniteDimensional ℝ (TangentSpace (𝓡 m) x) := by
  change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin m))
  infer_instance




def normalDerivativeShapeOperator (D : LeviCivitaData g)
    (h : RiemannianMetric m L) (F : L → M)
    (N : (x : M) → TangentSpace (𝓡 n) x) (x : L) :
    TangentSpace (𝓡 m) x →ₗ[ℝ] TangentSpace (𝓡 m) x :=
  (h.inner x).inverse.toLinearMap.comp
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (LinearMap.mk₂ ℝ
        (fun u v => g.inner (F x)
          (D.connection N (F x) (mfderiv (𝓡 m) (𝓡 n) F x u))
          (mfderiv (𝓡 m) (𝓡 n) F x v))
        (by intros; simp [map_add]) (by intros; simp [map_smul])
        (by intros; simp [map_add]) (by intros; simp [map_smul])))

theorem inner_normalDerivativeShapeOperator (D : LeviCivitaData g)
    (h : RiemannianMetric m L) (F : L → M)
    (N : (x : M) → TangentSpace (𝓡 n) x) (x : L)
    (u v : TangentSpace (𝓡 m) x) :
    h.inner x (D.normalDerivativeShapeOperator h F N x u) v =
      g.inner (F x) (D.connection N (F x) (mfderiv (𝓡 m) (𝓡 n) F x u))
        (mfderiv (𝓡 m) (𝓡 n) F x v) := by
  exact congrArg (fun A => A v) ((h.inner_isInvertible x).self_apply_inverse _)

end PoincareConjecture.LeviCivitaData

namespace Poincare.Geometry.Curvature.Hypersurface

open PoincareConjecture

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)



theorem normalDerivativeShapeOperator_eq_shapeOperator_neg
    {m n : ℕ} {g : RiemannianMetric n (E n)} {h : RiemannianMetric m (E m)}
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E m → E n} {N : E n → E n} {x : E m}
    (hF : ContDiffAt ℝ ∞ F x) (hN : DifferentiableAt ℝ N (F x))
    (hNT : ∀ᶠ y in 𝓝 x, ∀ v, g.inner (F y) (N (F y)) (fderiv ℝ F y v) = 0) :
    D.normalDerivativeShapeOperator h F N x = shapeOperator D D' F x (-N (F x)) := by
  apply LinearMap.ext
  intro u
  apply (h.inner_isInvertible x).injective
  apply ContinuousLinearMap.ext
  intro v
  rw [D.inner_normalDerivativeShapeOperator]
  have hd := inner_shapeOperator_neg_normal_eq_normal_derivative D D' hF
    (hN.comp x (hF.differentiableAt (by simp))) hNT u v
  simp only [Function.comp_apply] at hd
  erw [hd]
  erw [mfderiv_eq_fderiv, D.connection_eq_fderiv_add hN]
  unfold covariantDerivativeAlongMap
  rw [fderiv_comp x hN (hF.differentiableAt (by simp))]
  rfl

end Poincare.Geometry.Curvature.Hypersurface

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M} (D : LeviCivitaData g)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M) (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
  (c : ℝ)

local instance ambient_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩



def regularLevelShapeOperator (z : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    TangentSpace (𝓡 n) z →ₗ[ℝ] TangentSpace (𝓡 n) z := by
  letI := openLevelSetChartedSpace hf U hreg n c
  letI := isManifold_openLevelSet hf U hreg n c
  exact D.normalDerivativeShapeOperator (RiemannianMetric.regularLevelMetric hf U hreg c g)
    (openLevelIncl f U c) (D.levelUnitNormal f) z

theorem inner_gradient_regularLevelIncl (z : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    ∀ v : TangentSpace (𝓡 n) z,
    g.inner (openLevelIncl f U c z) (D.gradient f (openLevelIncl f U c z))
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) z v) = 0 := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  intro v
  have hrange := range_mfderiv_openLevelIncl hf U hreg n c z
  have hv : mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) z v ∈
      (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f (openLevelIncl f U c z)).ker := by
    rw [← hrange]
    exact ⟨v, rfl⟩
  rw [D.inner_gradient]
  change mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f (openLevelIncl f U c z)
    (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) z v) = 0 at hv
  change NormedSpace.fromTangentSpace (f (openLevelIncl f U c z))
    ((mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f (openLevelIncl f U c z))
      (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) z v)) = 0
  rw [hv, map_zero]

include hreg in
theorem regularLevel_levelQ_pos (z : openLevelSet f U c) :
    0 < D.levelQ f (openLevelIncl f U c z) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold levelQ
  have hgrad : D.gradient f (openLevelIncl f U c z) ≠ 0 := by
    intro hz
    exact hreg _ z.1.property
      ((g.gradient_eq_zero_iff_mfderiv_eq_zero f (openLevelIncl f U c z)).mp hz)
  exact real_inner_self_pos.mpr hgrad

include hreg in

theorem inner_regularLevelUnitNormal_self (z : openLevelSet f U c) :
    g.inner (openLevelIncl f U c z)
      (D.levelUnitNormal f (openLevelIncl f U c z))
      (D.levelUnitNormal f (openLevelIncl f U c z)) = 1 := by
  have hQ := D.regularLevel_levelQ_pos U hreg c z
  have hr := (Real.sqrt_pos.2 hQ).ne'
  have hrq := Real.sq_sqrt hQ.le
  rw [levelUnitNormal]
  simp only [map_smul, smul_apply, smul_eq_mul]
  change (Real.sqrt (D.levelQ f (openLevelIncl f U c z)))⁻¹ *
    ((Real.sqrt (D.levelQ f (openLevelIncl f U c z)))⁻¹ *
      D.levelQ f (openLevelIncl f U c z)) = 1
  field_simp
  exact hrq.symm


theorem inner_regularLevelUnitNormal_tangent (z : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    ∀ v : TangentSpace (𝓡 n) z,
      g.inner (openLevelIncl f U c z)
        (D.levelUnitNormal f (openLevelIncl f U c z))
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) z v) = 0 := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  intro v
  rw [levelUnitNormal]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [D.inner_gradient_regularLevelIncl hf U hreg c z v, mul_zero]



theorem inner_regularLevelShapeOperator (z : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    ∀ u v : TangentSpace (𝓡 n) z,
    (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z
        (D.regularLevelShapeOperator hf U hreg c z u) v =
      D.hessian f (openLevelIncl f U c z)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) z u)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) z v) /
      Real.sqrt (D.levelQ f (openLevelIncl f U c z)) := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  intro u v
  unfold regularLevelShapeOperator
  rw [D.inner_normalDerivativeShapeOperator]
  exact D.inner_connection_unitNormal hf _ (D.regularLevel_levelQ_pos U hreg c z)
    _ _ (D.inner_gradient_regularLevelIncl hf U hreg c z v)


theorem inner_regularLevelShapeOperator_eq_levelSecondFundamental
    (z : openLevelSet f U c) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    ∀ u v : TangentSpace (𝓡 n) z,
      (RiemannianMetric.regularLevelMetric hf U hreg c g).inner z
          (D.regularLevelShapeOperator hf U hreg c z u) v =
        D.levelSecondFundamental f (openLevelIncl f U c z)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) z u)
          (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) z v) := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  intro u v
  rw [D.inner_regularLevelShapeOperator hf U hreg c z u v]
  simp only [levelSecondFundamental, levelProjection,
    D.inner_regularLevelUnitNormal_tangent hf U hreg c z, zero_smul, sub_zero]



theorem regularLevelShapeOperator_eq_id (z : openLevelSet f U c)
    (hH : ∀ u v, D.hessian f (openLevelIncl f U c z) u v =
      g.inner (openLevelIncl f U c z) u v)
    (hQ : D.levelQ f (openLevelIncl f U c z) = 1) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    D.regularLevelShapeOperator hf U hreg c z = LinearMap.id := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  apply LinearMap.ext
  intro u
  apply ((RiemannianMetric.regularLevelMetric hf U hreg c g).inner_isInvertible z).injective
  apply ContinuousLinearMap.ext
  intro v
  rw [D.inner_regularLevelShapeOperator hf U hreg c z u v, hH, hQ]
  simp only [Real.sqrt_one, div_one, LinearMap.id_apply]
  rfl



theorem radialLevelShapeOperator_eq_id
    (hH : ∀ x ∈ U, ∀ u v, D.hessian f x u v = g.inner x u v)
    (hQ : ∀ x ∈ U, f x = 1 / 2 → D.levelQ f x = 1)
    (z : openLevelSet f U (1 / 2)) :
    letI := openLevelSetChartedSpace hf U hreg n (1 / 2)
    letI := isManifold_openLevelSet hf U hreg n (1 / 2)
    D.regularLevelShapeOperator hf U hreg (1 / 2) z = LinearMap.id := by
  let := openLevelSetChartedSpace hf U hreg n (1 / 2)
  let := isManifold_openLevelSet hf U hreg n (1 / 2)
  exact D.regularLevelShapeOperator_eq_id hf U hreg (1 / 2) z
    (hH _ z.1.property) (hQ _ z.1.property z.property)

end PoincareConjecture.LeviCivitaData
