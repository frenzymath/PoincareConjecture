import PoincareConjecture.Proofs.M10.PreferredHessian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv










set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem scalar_field_derivative_mdifferentiableAt {f : M → ℝ} {q : M}
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f q)
    {Y : (x : M) → TangentSpace (𝓡 n) x}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun x ↦ (⟨x, Y x⟩ : TangentBundle (𝓡 n) M)) q) :
    MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun x ↦ mvfderiv (𝓡 n) f x (Y x)) q := by
  have hD := (hf.mfderiv_const (m := 1) (by norm_num)).mdifferentiableAt one_ne_zero
  have hE := hD.clm_apply_of_inCoordinates hY (hf.mdifferentiableAt two_ne_zero)
  have hs := (contMDiff_snd_tangentBundle_modelSpace ℝ (𝓘(ℝ, ℝ)) (n := 1)).mdifferentiable
    one_ne_zero
  exact (hs (⟨f q, mfderiv (𝓡 n) (𝓘(ℝ, ℝ)) f q (Y q)⟩ :
    TangentBundle (𝓘(ℝ, ℝ)) ℝ)).comp q hE

set_option backward.isDefEq.respectTransparency false in

theorem hessian_field_tensorial (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {f : M → ℝ} {q : M} (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f q)
    (u : TangentSpace (𝓡 n) q) :
    TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (fun Y : (x : M) → TangentSpace (𝓡 n) x ↦
        mvfderiv (𝓡 n) (fun x ↦ mvfderiv (𝓡 n) f x (Y x)) q u -
          mvfderiv (𝓡 n) f q (D.connection Y q u)) q := by
  constructor
  · intro a Y ha hY
    have heq : (fun x ↦ mvfderiv (𝓡 n) f x ((a • Y) x)) =
        (fun x ↦ a x * mvfderiv (𝓡 n) f x (Y x)) := by
      funext x
      change mvfderiv (𝓡 n) f x (a x • Y x) = _
      exact (mvfderiv (𝓡 n) f x).map_smul (a x) (Y x)
    rw [heq, mvfderiv_fun_mul ha (scalar_field_derivative_mdifferentiableAt hf hY),
      D.connection.isCovariantDerivativeOnUniv.leibniz hY ha]
    simp only [_root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_eq_mul]
    ring
  · intro Y Z hY hZ
    have heq : (fun x ↦ mvfderiv (𝓡 n) f x ((Y + Z) x)) =
        (fun x ↦ mvfderiv (𝓡 n) f x (Y x) + mvfderiv (𝓡 n) f x (Z x)) := by
      funext x
      simp only [Pi.add_apply, map_add]
    rw [heq, mvfderiv_fun_add (scalar_field_derivative_mdifferentiableAt hf hY)
      (scalar_field_derivative_mdifferentiableAt hf hZ),
      D.connection.isCovariantDerivativeOnUniv.add hY hZ]
    simp only [_root_.add_apply, map_add]
    ring

set_option backward.isDefEq.respectTransparency false in

theorem hessian_eq_of_extension (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {f : M → ℝ} {q : M} (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f q)
    (u : TangentSpace (𝓡 n) q) {Y : (x : M) → TangentSpace (𝓡 n) x}
    (hY : MDifferentiableAt (𝓡 n) (𝓡 n).tangent
      (fun x ↦ (⟨x, Y x⟩ : TangentBundle (𝓡 n) M)) q) :
    D.hessian f q u (Y q) =
      mvfderiv (𝓡 n) (fun x ↦ mvfderiv (𝓡 n) f x (Y x)) q u -
        mvfderiv (𝓡 n) f q (D.connection Y q u) := by
  have hext := FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (Y q)
  have h := (hessian_field_tensorial g D hf u).pointwise hY hext
    (FiberBundle.extend_apply_self (EuclideanSpace ℝ (Fin n)) (Y q)).symm
  simpa only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
    FiberBundle.extend_apply_self] using h.symm

end PoincareConjecture.M10
