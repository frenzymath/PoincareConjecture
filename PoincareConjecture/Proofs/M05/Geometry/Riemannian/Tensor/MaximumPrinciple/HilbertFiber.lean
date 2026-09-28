
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Norm
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Analysis.InnerProductSpace.PiL2












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators InnerProductSpace

namespace PoincareConjecture


def TensorFiber (E : Type*) [AddCommGroup E] [Module ℝ E] (k : ℕ) :=
  MultilinearMap ℝ (fun _ : Fin k => E) ℝ

namespace TensorFiber

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}

instance : AddCommGroup (TensorFiber E k) :=
  inferInstanceAs (AddCommGroup (MultilinearMap ℝ (fun _ : Fin k => E) ℝ))

instance : Module ℝ (TensorFiber E k) :=
  inferInstanceAs (Module ℝ (MultilinearMap ℝ (fun _ : Fin k => E) ℝ))


def toMultilinear : TensorFiber E k ≃ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin k => E) ℝ :=
  LinearEquiv.refl ℝ _

instance : CoeFun (TensorFiber E k) (fun _ => (Fin k → E) → ℝ) :=
  ⟨fun T => toMultilinear T⟩

@[simp] lemma toMultilinear_apply (T : TensorFiber E k) (v : Fin k → E) :
    toMultilinear T v = T v := rfl

@[ext] lemma ext {T S : TensorFiber E k} (h : ∀ v, T v = S v) : T = S :=
  toMultilinear.injective (MultilinearMap.ext h)

@[simp] lemma add_apply (T S : TensorFiber E k) (v : Fin k → E) :
    (T + S) v = T v + S v := rfl

@[simp] lemma smul_apply (c : ℝ) (T : TensorFiber E k) (v : Fin k → E) :
    (c • T) v = c * T v := rfl

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


noncomputable def components (k : ℕ) : TensorFiber E k →ₗ[ℝ]
    EuclideanSpace ℝ (Fin k → Fin (Module.finrank ℝ E)) where
  toFun T := WithLp.toLp 2 (fun a => T (fun i => stdOrthonormalBasis ℝ E (a i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma components_injective (k : ℕ) : Function.Injective (components (E := E) k) := by
  intro T S h
  apply toMultilinear.injective
  apply Module.Basis.ext_multilinear (fun _ => (stdOrthonormalBasis ℝ E).toBasis)
  intro a
  exact congrArg (fun z : EuclideanSpace ℝ (Fin k → Fin (Module.finrank ℝ E)) => z a) h

noncomputable instance : NormedAddCommGroup (TensorFiber E k) :=
  NormedAddCommGroup.induced _ _ (components (E := E) k) (components_injective k)

noncomputable instance : InnerProductSpace ℝ (TensorFiber E k) :=
  InnerProductSpace.induced (components (E := E) k)

instance : FiniteDimensional ℝ (TensorFiber E k) :=
  FiniteDimensional.of_injective (components (E := E) k) (components_injective k)

instance : CompleteSpace (TensorFiber E k) := FiniteDimensional.complete ℝ _


theorem inner_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T S : TensorFiber E k) :
    ⟪T, S⟫_ℝ = ∑ a : Fin k → ι, T (fun i => b (a i)) * S (fun i => b (a i)) := by
  change ⟪components k T, components k S⟫_ℝ = _
  rw [PiLp.inner_apply]
  simp only [components, LinearMap.coe_mk, AddHom.coe_mk,
    RCLike.inner_apply, conj_trivial]
  simpa only [mul_comm] using multilinear_sum_mul_orthonormalBasis_eq
    (toMultilinear T) (toMultilinear S) (stdOrthonormalBasis ℝ E) b


theorem norm_eq_sqrt_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T : TensorFiber E k) :
    ‖T‖ = Real.sqrt (∑ a : Fin k → ι, (T (fun i => b (a i))) ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg T), ← real_inner_self_eq_norm_sq, inner_eq_sum b]
  simp only [pow_two]

end Hilbert

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]


noncomputable def transportLinear (e : E ≃ₗᵢ[ℝ] F) (k : ℕ) :
    TensorFiber E k ≃ₗ[ℝ] TensorFiber F k :=
  toMultilinear.trans ((LinearEquiv.multilinearMapCongrLeft
    (fun _ : Fin k => e.symm.toLinearEquiv)).trans toMultilinear.symm)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp] lemma transportLinear_apply (e : E ≃ₗᵢ[ℝ] F) (T : TensorFiber E k)
    (v : Fin k → F) : transportLinear e k T v = T (fun i => e.symm (v i)) := rfl

lemma transportLinear_inner (e : E ≃ₗᵢ[ℝ] F) (T S : TensorFiber E k) :
    ⟪transportLinear e k T, transportLinear e k S⟫_ℝ = ⟪T, S⟫_ℝ := by
  rw [inner_eq_sum ((stdOrthonormalBasis ℝ E).map e),
    inner_eq_sum (stdOrthonormalBasis ℝ E)]
  simp only [transportLinear_apply, OrthonormalBasis.map_apply, e.symm_apply_apply]


noncomputable def transport (e : E ≃ₗᵢ[ℝ] F) (k : ℕ) :
    TensorFiber E k ≃ₗᵢ[ℝ] TensorFiber F k :=
  LinearEquiv.isometryOfInner (transportLinear e k) (transportLinear_inner e)

@[simp] lemma transport_apply (e : E ≃ₗᵢ[ℝ] F) (T : TensorFiber E k)
    (v : Fin k → F) : transport e k T v = T (fun i => e.symm (v i)) := rfl



theorem inner_transport_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (e : E ≃ₗᵢ[ℝ] F)
    (N : TensorFiber E k) (T : TensorFiber F k) :
    ⟪transport e k N, T⟫_ℝ =
      ∑ a : Fin k → ι, N (fun i => b (a i)) * T (fun i => e (b (a i))) := by
  rw [inner_eq_sum (b.map e)]
  simp only [transport_apply, OrthonormalBasis.map_apply, e.symm_apply_apply]

end Transport

end TensorFiber

end PoincareConjecture
