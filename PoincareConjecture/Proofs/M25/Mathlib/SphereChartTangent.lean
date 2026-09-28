import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Transition
import Mathlib.Geometry.Manifold.MFDeriv.Atlas










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open PoincareConjecture
open scoped Manifold ContDiff

namespace Poincare.Geometry.Riemannian.SpaceForm



theorem sphere_chart_symm_mfderiv_zero {n : ℕ} (q : UnitSphere n) :
    mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm 0 =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  have h := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := q)
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp,
    Set.range_id, mfderivWithin_univ] at h
  change mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    (chartAt (EuclideanSpace ℝ (Fin n)) q q) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) at h
  rwa [sphere_chart_center] at h



theorem norm_mfderiv_sphere_inclusion {n : ℕ} (q : UnitSphere n)
    (v : TangentSpace (𝓡 n) q) :
    (norm : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      (mfderiv (𝓡 n) (𝓡 (n + 1))
        (Subtype.val : UnitSphere n → EuclideanSpace ℝ (Fin (n + 1))) q v) =
      (norm : EuclideanSpace ℝ (Fin n) → ℝ) v := by
  have h := roundSphereMetric_chart_symm_inner q 0 v v
  rw [sphere_chart_symm_mfderiv_zero] at h
  change (roundSphereMetric n).inner
    ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm 0) v v =
      16 / (‖(0 : EuclideanSpace ℝ (Fin n))‖ ^ 2 + 4) ^ 2 *
        (inner ℝ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ) v v at h
  rw [sphere_chart_symm_zero, roundSphereMetric_inner,
    RiemannianMetric.euclideanMetric_inner] at h
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
  norm_num at h
  exact h

end Poincare.Geometry.Riemannian.SpaceForm
