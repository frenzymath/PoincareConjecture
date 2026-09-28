import PoincareConjecture.Proofs.M35.RadialGauge.GaussianCoordinates
import PoincareConjecture.Proofs.M35.RadialGauge.HeatWeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))

theorem integral_stdGaussian_eq_pi (f : V → F) :
    (∫ z, f z ∂stdGaussian V) =
      ∫ z : Fin (n + 1) → ℝ, f (WithLp.toLp 2 z)
        ∂Measure.pi fun _ => gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian]
  exact (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).measurableEmbedding.integral_map f

private theorem hasDerivAt_insert_euclidean (i : Fin (n + 1)) (z : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun a : ℝ => WithLp.toLp 2 (i.insertNth (α := fun _ => ℝ) a z))
      (EuclideanSpace.single i (1 : ℝ)) s := by
  have heq : (fun a : ℝ => WithLp.toLp 2 (i.insertNth (α := fun _ => ℝ) a z)) =
      fun a => a • EuclideanSpace.single i (1 : ℝ) +
        WithLp.toLp 2 (i.insertNth (α := fun _ => ℝ) 0 z) := by
    funext a
    apply PiLp.ext
    intro j
    rcases i.eq_self_or_eq_succAbove j with rfl | ⟨k, rfl⟩ <;> simp
  rw [heq]
  simpa using ((hasDerivAt_id s).smul_const (EuclideanSpace.single i (1 : ℝ))).add_const
    (WithLp.toLp 2 (i.insertNth (α := fun _ => ℝ) 0 z))

theorem integral_stdGaussian_coordinate_derivative (i : Fin (n + 1))
    {f : V → F} {f' : V → V →L[ℝ] F} (hf : Continuous f) (hf' : Continuous f')
    (hderiv : ∀ x, HasFDerivAt f (f' x) x)
    {C D : ℝ} (hbound : ∀ x, ‖f x‖ ≤ C) (hdbound : ∀ x, ‖f' x‖ ≤ D) :
    (∫ z, f' z (EuclideanSpace.single i (1 : ℝ)) ∂stdGaussian V) =
      ∫ z, z i • f z ∂stdGaussian V := by
  rw [integral_stdGaussian_eq_pi, integral_stdGaussian_eq_pi]
  refine integral_pi_gaussian_coordinate_derivative (C := C) (D := D) i
    (hf.comp (PiLp.continuous_toLp 2 _))
    ((hf'.comp (PiLp.continuous_toLp 2 _)).clm_apply continuous_const)
    (fun x => hbound _) ?_ ?_
  · intro x
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    simpa using hdbound (WithLp.toLp 2 x)
  · intro z s
    exact (hderiv _).comp_hasDerivAt s (hasDerivAt_insert_euclidean i z s)

end PoincareConjecture.M35.RadialGauge
