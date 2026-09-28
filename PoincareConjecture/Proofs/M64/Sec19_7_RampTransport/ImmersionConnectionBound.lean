import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Connection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture

open Poincare.Geometry.Curvature.Hypersurface

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
  {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))}

theorem m64_induced_connection_norm_le
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {Y : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin m)} (hF : ContDiffAt ℝ ∞ F x)
    (hY : DifferentiableAt ℝ Y x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (u : EuclideanSpace ℝ (Fin m)) :
    h.tangentNorm x (Dh.connection Y x u) ≤
      g.tangentNorm (F x)
        (covariantDerivativeAlongMap D F (fun y => fderiv ℝ F y (Y y)) x u) := by
  let B := secondFundamentalForm D Dh F x u (Y x)
  let V := fderiv ℝ F x (Dh.connection Y x u)
  have hdecomp : covariantDerivativeAlongMap D F (fun y => fderiv ℝ F y (Y y)) x u =
      B + V := by
    exact (sub_eq_iff_eq_add.mp
      (secondFundamentalForm_eq_covariantDerivativeAlongMap D Dh hF hY u).symm)
  have horth : g.inner (F x) B V = 0 :=
    secondFundamentalForm_normal D Dh hF hmetric u (Y x) (Dh.connection Y x u)
  have horth' : g.inner (F x) V B = 0 := (g.symm (F x) V B).trans horth
  have hnonneg : 0 ≤ g.inner (F x) B B := by
    by_cases hB : B = 0
    · simp only [hB, map_zero, le_refl]
    · exact (g.pos (F x) B hB).le
  unfold RiemannianMetric.tangentNorm
  apply Real.sqrt_le_sqrt
  simp only [hdecomp, map_add, add_apply, horth, horth', zero_add, add_zero]
  rw [hmetric.self_of_nhds]
  exact le_add_of_nonneg_left hnonneg

end PoincareConjecture
