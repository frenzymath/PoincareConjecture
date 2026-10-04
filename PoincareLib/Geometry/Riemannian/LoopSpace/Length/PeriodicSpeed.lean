import PoincareLib.Geometry.Riemannian.LoopSpace.Length.Angular
import PoincareLib.Topology.VectorBundle.CompactDisk
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The speed integral over a shifted angular period

Mathlib's polar angle ranges from minus pi to pi. Morgan--Tian's loop length
in Corollary 18.28, printed p. 434, uses the fixed period from zero to two pi.
We prove the exact bridge using periodicity of the actual manifold tangent
map. See the task's polar-area derivation.
-/

set_option autoImplicit false

open Set MeasureTheory Bundle Real
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.LoopSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The frozen angular representative is periodic as an actual manifold
map. Source: MT Definition 18.17, p. 430, circle convention. -/
theorem periodic_periodicFreeLoop (γ : C1FreeLoopSpace (M := M)) :
    Function.Periodic (periodicFreeLoop γ) rampPeriod := by
  intro t
  simp [periodicFreeLoop, rampPeriod, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The speed in the specified metric is periodic. Source:
MT Corollary 18.28, p. 434, polar-area derivation. -/
theorem periodic_freeLoopSpeed (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) :
    Function.Periodic (fun t => g.tangentNorm (periodicFreeLoop γ t)
      (curveVelocity (periodicFreeLoop γ) t)) rampPeriod := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro t
  let a : ℝ → ℝ := fun s => s + rampPeriod
  have ha : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t :=
    ((contDiff_id.add contDiff_const).contDiffAt : ContDiffAt ℝ ∞ a t).contMDiffAt.mdifferentiableAt
      (by simp)
  have hda : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t (1 : ℝ) = 1 := by
    simpa +instances only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using!
      ((hasDerivAt_id t).add_const rampPeriod).deriv
  have heq : periodicFreeLoop γ ∘ a = periodicFreeLoop γ :=
    funext (periodic_periodicFreeLoop γ)
  have ht := tangentMap_comp_at (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓡 3)
    (f := a) (g := periodicFreeLoop γ) (⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)
    ((contMDiff_periodicFreeLoop γ (a t)).mdifferentiableAt one_ne_zero) ha
  rw [heq] at ht
  have hinput : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a ⟨t, 1⟩ =
      (⟨t + rampPeriod, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) := by
    change (⟨t + rampPeriod, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) a t 1⟩ :
      TangentBundle 𝓘(ℝ, ℝ) ℝ) = _
    erw [hda]
  rw [hinput] at ht
  exact (congrArg (fun v : TangentBundle (𝓡 3) M => ‖v.2‖) ht).symm

/-- The polar angular speed integral is exactly the contract's length.
Source: MT Corollary 18.28, p. 434, polar-area derivation. -/
theorem integral_polar_freeLoopSpeed (g : RiemannianMetric 3 M)
    (γ : C1FreeLoopSpace (M := M)) :
    (∫ t in Ioo (-π) π, g.tangentNorm (periodicFreeLoop γ t)
      (curveVelocity (periodicFreeLoop γ) t)) = freeLoopLength g γ := by
  have h := (periodic_freeLoopSpeed g γ).intervalIntegral_add_eq (-π) 0
  have hends : -π + rampPeriod = π := by dsimp [rampPeriod]; ring
  rw [hends, zero_add] at h
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo] at h
  exact h

end PoincareMT.LoopSpace
