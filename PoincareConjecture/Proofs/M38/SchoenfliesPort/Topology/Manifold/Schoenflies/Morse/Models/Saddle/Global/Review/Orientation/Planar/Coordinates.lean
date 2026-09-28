import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Reflection
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.SaddleLevel
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
open Poincare.Geometry.Euclidean
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem heightReflection_eq_reflection {v : E3} (hv : ‖v‖ = 1) (x : E3) :
    heightReflection hv x = (Real ∙ v)ᗮ.reflection x := by
  rw [heightReflection, liftPlaneDiffeomorph_apply, Submodule.reflection_apply]
  have hsplit := (Real ∙ v).starProjection_add_starProjection_orthogonal x
  rw [Submodule.starProjection_unit_singleton Real hv] at hsplit
  change (0 + -1 * inner Real v x) • v +
      (Real ∙ v)ᗮ.starProjection x = 2 • (Real ∙ v)ᗮ.starProjection x - x
  simp only [zero_add, neg_one_mul, neg_smul]
  calc
    _ = 2 • (Real ∙ v)ᗮ.starProjection x -
        (inner Real v x • v + (Real ∙ v)ᗮ.starProjection x) := by module
    _ = _ := by rw [hsplit]

theorem heightReflection_isometry {v : E3} (hv : ‖v‖ = 1) :
    Isometry (heightReflection hv) := by
  have heq : (heightReflection hv : E3 → E3) = (Real ∙ v)ᗮ.reflection :=
    funext (heightReflection_eq_reflection hv)
  rw [heq]
  exact (Real ∙ v)ᗮ.reflection.isometry

@[simp] theorem heightReflection_zero {v : E3} (hv : ‖v‖ = 1) :
    heightReflection hv 0 = 0 := by
  rw [heightReflection_eq_reflection, map_zero]

theorem Rz_isometry : Isometry Rz := by
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  ring

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview

end

end M38Schoenflies
