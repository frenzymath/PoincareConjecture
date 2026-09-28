import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Gauss
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture

open Poincare.Geometry.Curvature.Hypersurface

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64_secondFundamental_sum_eq_zero_of_harmonic
    {m n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)}
    (hF : ContDiffAt ℝ ∞ F x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (u v : EuclideanSpace ℝ (Fin m))
    (hharm : covariantHessianMap D F x u u + covariantHessianMap D F x v v = 0) :
    secondFundamentalForm D Dh F x u u + secondFundamentalForm D Dh F x v v = 0 := by
  let S := secondFundamentalForm D Dh F x u u + secondFundamentalForm D Dh F x v v
  let w := -(Dh.connectionCoefficient x u u + Dh.connectionCoefficient x v v)
  have heq : S = fderiv ℝ F x w := by
    dsimp only [S, w, secondFundamentalForm]
    rw [map_neg, map_add, sub_add_sub_comm, hharm, zero_sub]
  have hnormal : g.inner (F x) S (fderiv ℝ F x w) = 0 := by
    simp only [S, map_add, add_apply,
      secondFundamentalForm_normal D Dh hF hmetric, add_zero]
  rw [← heq] at hnormal
  by_contra hne
  exact (ne_of_gt (g.pos (F x) S hne)) hnormal





theorem m64_minimal_surface_gaussian_le_sectional
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {h : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin 2)}
    (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (u v : EuclideanSpace ℝ (Fin 2))
    (hu : h.inner x u u = 1) (hv : h.inner x v v = 1) (huv : h.inner x u v = 0)
    (hmean : secondFundamentalForm D Dh F x u u + secondFundamentalForm D Dh F x v v = 0) :
    Dh.scalarCurvature x / 2 ≤
      D.sectionalCurvature (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) := by
  have hsource : Dh.curvatureTensor x u v u v = Dh.scalarCurvature x / 2 := by
    rw [Dh.curvatureTensor_eq_half_scalarCurvature, hu, hv, huv, h.symm x v u, huv]
    ring
  have hambient : D.sectionalCurvature (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) =
      D.curvatureTensor (F x) (fderiv ℝ F x u) (fderiv ℝ F x v)
        (fderiv ℝ F x u) (fderiv ℝ F x v) := by
    unfold LeviCivitaData.sectionalCurvature
    rw [← hmetric.self_of_nhds u u, ← hmetric.self_of_nhds v v,
      ← hmetric.self_of_nhds u v, hu, hv, huv]
    norm_num
  have htrace : secondFundamentalForm D Dh F x v v = -secondFundamentalForm D Dh F x u u := by
    rw [eq_neg_iff_add_eq_zero]
    simpa only [add_comm] using hmean
  have hnonneg (w : EuclideanSpace ℝ (Fin n)) : 0 ≤ g.inner (F x) w w := by
    by_cases hw : w = 0
    · simp only [hw, map_zero, le_refl]
    · exact (g.pos (F x) w hw).le
  have hgauss := gauss_curvatureTensor_of_eventually D Dh hF hmetric u v u v
  rw [hsource, htrace, map_neg,
    secondFundamentalForm_symm D Dh hF.self_of_nhds v u] at hgauss
  rw [hambient]
  linarith only [hgauss, hnonneg (secondFundamentalForm D Dh F x u u),
    hnonneg (secondFundamentalForm D Dh F x u v)]




theorem m64_harmonic_surface_gaussian_le_sectional
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {h : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))}
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin 2)}
    (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (u v : EuclideanSpace ℝ (Fin 2))
    (hu : h.inner x u u = 1) (hv : h.inner x v v = 1) (huv : h.inner x u v = 0)
    (hharm : covariantHessianMap D F x u u + covariantHessianMap D F x v v = 0) :
    Dh.scalarCurvature x / 2 ≤
      D.sectionalCurvature (F x) (fderiv ℝ F x u) (fderiv ℝ F x v) :=
  m64_minimal_surface_gaussian_le_sectional D Dh hF hmetric u v hu hv huv
    (m64_secondFundamental_sum_eq_zero_of_harmonic D Dh hF.self_of_nhds hmetric u v hharm)

end PoincareConjecture
