import PoincareConjecture.Definitions.Ch06.LGeometry
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem curveVelocity_congr_of_eventuallyEq {γ δ : ℝ → M} {t : ℝ}
    (heq : γ =ᶠ[nhds t] δ) :
    (curveVelocity (n := n) γ t : EuclideanSpace ℝ (Fin n)) = curveVelocity (n := n) δ t := by
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
  exact congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ L 1) hd

set_option backward.isDefEq.respectTransparency false in
theorem curveVelocity_comp_initial_line {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → M) (Z W : E)
    (hf : MDifferentiableAt (𝓘(ℝ, E)) (𝓡 n) f Z) :
    (curveVelocity (n := n) (fun r : ℝ ↦ f (Z + r • W)) 0 : EuclideanSpace ℝ (Fin n)) =
      mfderiv (𝓘(ℝ, E)) (𝓡 n) f Z W := by
  have hline : HasDerivAt (fun r : ℝ ↦ Z + r • W) W 0 := by
    have hsmul : HasDerivAt (fun r : ℝ ↦ r • W) W 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const W
    exact hsmul.const_add Z
  have hvalue : (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun r : ℝ ↦ Z + r • W) 0) 1 = W := by
    exact (congrArg (fun L : ℝ →L[ℝ] E ↦ L 1)
      (mfderiv_eq_fderiv (f := fun r : ℝ ↦ Z + r • W) (x := 0))).trans
      ((congrArg (fun L : ℝ →L[ℝ] E ↦ L 1) hline.hasFDerivAt.fderiv).trans
        (ContinuousLinearMap.toSpanSingleton_apply_one ℝ W))
  have hf' : MDifferentiableAt (𝓘(ℝ, E)) (𝓡 n) f (Z + (0 : ℝ) • W) := by
    simpa only [zero_smul, add_zero] using hf
  have hcomp := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ L 1)
    (mfderiv_comp (f := fun r : ℝ ↦ Z + r • W) (g := f)
      0 hf' hline.hasFDerivAt.hasMFDerivAt.mdifferentiableAt)
  have hresult := hcomp.trans (congrArg
    (fun v : E ↦ mfderiv (𝓘(ℝ, E)) (𝓡 n) f (Z + (0 : ℝ) • W) v) hvalue)
  have hpoint := congrArg (fun L : E →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ L W)
    (mfderiv_congr_point (I := 𝓘(ℝ, E)) (I' := 𝓡 n) (f := f)
      (show Z + (0 : ℝ) • W = Z by simp))
  exact hresult.trans hpoint

set_option backward.isDefEq.respectTransparency false in
theorem curveVelocity_comp_square (α : ℝ → M) (s : ℝ)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α (s ^ 2)) :
    curveVelocity (n := n) (fun r ↦ α (r ^ 2)) s =
      (2 * s) • curveVelocity (n := n) α (s ^ 2) := by
  have hsq : HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hvalue : (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ ↦ r ^ 2) s) 1 = 2 * s := by
    exact (congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1)
      (mfderiv_eq_fderiv (f := fun r : ℝ ↦ r ^ 2) (x := s))).trans
      ((congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hsq.hasFDerivAt.fderiv).trans
        (ContinuousLinearMap.toSpanSingleton_apply_one ℝ (2 * s)))
  let L : ℝ →L[ℝ] TangentSpace (𝓡 n) (α (s ^ 2)) :=
    mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) α (s ^ 2)
  have hcomp := congrArg (fun A : ℝ →L[ℝ] TangentSpace (𝓡 n) (α (s ^ 2)) ↦ A 1)
    (mfderiv_comp (f := fun r : ℝ ↦ r ^ 2) (g := α)
      s hα hsq.hasFDerivAt.hasMFDerivAt.mdifferentiableAt)
  have hlin : L (2 * s) = (2 * s) • L 1 := by
    simpa only [smul_eq_mul, mul_one] using L.map_smul (2 * s) (1 : ℝ)
  exact hcomp.trans ((congrArg L hvalue).trans hlin)

end PoincareConjecture.Proofs.M09
