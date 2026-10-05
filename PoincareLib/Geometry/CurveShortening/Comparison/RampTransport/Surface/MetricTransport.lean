import PoincareLib.Geometry.Curvature.Hypersurface.Charts
import PoincareLib.Geometry.Curvature.Hypersurface.Sectional
import PoincareLib.Geometry.Riemannian.Surface.Curvature
import PoincareLib.Geometry.Riemannian.Coordinates.Orthonormal

/-! Gaussian curvature transport for actual induced surface metric germs.
Source: MT Lemma 19.31, pp. 464-466; trimmed-intrinsic-transport derivation,
Section 12. Invertibility follows from the positive metrics in equal dimension. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareMT

open Poincare.Geometry.Curvature.Hypersurface

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- Gaussian curvature is preserved by a local induced metric between
surfaces. Positivity derives differential invertibility from metric
agreement itself. Source: MT Lemma 19.31, pp. 464-466; transport Section 12. -/
theorem m64_gaussian_eq_of_induced_surface_germ
    {g h : RiemannianMetric 2 (EuclideanSpace ℝ (Fin 2))}
    (Dg : LeviCivitaData g) (Dh : LeviCivitaData h)
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {p : EuclideanSpace ℝ (Fin 2)} (hf : ContDiffAt ℝ ∞ f p)
    (hmetric : ∀ᶠ q in 𝓝 p, ∀ u v : EuclideanSpace ℝ (Fin 2), g.inner q u v =
      h.inner (f q) (fderiv ℝ f q u) (fderiv ℝ f q v)) :
    Dg.scalarCurvature p / 2 = Dh.scalarCurvature (f p) / 2 := by
  have hinv : ∀ᶠ q in 𝓝 p, (mfderiv (𝓡 2) (𝓡 2) f q).IsInvertible := by
    filter_upwards [hmetric] with q hq
    rw [mfderiv_eq_fderiv]
    have hi := fderiv_injective_of_pullback_metric hq
    have hs := LinearMap.surjective_of_injective (f := (fderiv ℝ f q).toLinearMap) hi
    change (fderiv ℝ f q).IsInvertible
    exact ⟨ContinuousLinearEquiv.ofBijective (fderiv ℝ f q)
      (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs), rfl⟩
  have hmetric' : ∀ᶠ q in 𝓝 p, ∀ u v : EuclideanSpace ℝ (Fin 2), g.inner q u v =
      h.inner (f q) (mfderiv (𝓡 2) (𝓡 2) f q u) (mfderiv (𝓡 2) (𝓡 2) f q v) := by
    filter_upwards [hmetric] with q hq u v
    simp only [mfderiv_eq_fderiv]
    convert! hq u v using 1
  obtain ⟨L, hL⟩ := g.exists_orthonormal_coordinate_frame p
  simp only [g.chartCoefficients_center] at hL
  let b (i : Fin 2) := L (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hb (i j : Fin 2) : g.inner p (b i) (b j) = if i = j then 1 else 0 := by
    rw [show g.inner p (b i) (b j) = _ from hL _ _]
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_ite i j
  have hR := Dg.curvatureTensor_eq_pullback_euclidean Dh hf.contMDiffAt hinv hmetric'
    (b 0) (b 1) (b 0) (b 1)
  rw [Dg.curvatureTensor_eq_half_scalarCurvature,
    Dh.curvatureTensor_eq_half_scalarCurvature] at hR
  simp only [← hmetric'.self_of_nhds, hb] at hR
  norm_num at hR
  linarith only [hR]

end PoincareMT
