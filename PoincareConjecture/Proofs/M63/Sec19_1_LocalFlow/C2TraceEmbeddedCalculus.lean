import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddingHessianVector
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurveTensorLeibniz
import Mathlib.Analysis.Calculus.Deriv.Prod










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle Manifold
open scoped Manifold ContDiff Bundle BigOperators

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι]

local notation "W" => EuclideanSpace ℝ ι





theorem hasDerivAt_embedding_pushforward {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {gamma : ℝ → M} {x : ℝ}
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma x)
    (Y : (s : ℝ) → TangentSpace (𝓡 n) (gamma s))
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun s => (⟨gamma s, Y s⟩ : TangentBundle (𝓡 n) M)) x) :
    HasDerivAt (fun s => (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma s) (Y s) : W))
      (HAdd.hAdd (α := W) (β := W) (γ := W)
        (coordinateHessian D e (gamma x) (curveVelocity gamma x) (Y x))
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma x)
          (rampHorizontalCovariantDerivative D gamma Y x))) x := by
  classical
  have hcoord (i : ι) :
      HasDerivAt (fun s => EuclideanSpace.proj i
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma s) (Y s)))
        (EuclideanSpace.proj i (HAdd.hAdd (α := W) (β := W) (γ := W)
          (coordinateHessian D e (gamma x) (curveVelocity gamma x) (Y x))
          (mfderiv (𝓡 n) 𝓘(ℝ, W) e (gamma x)
            (rampHorizontalCovariantDerivative D gamma Y x)))) x := by
    let f : M → ℝ := fun p => e p i
    have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f :=
      (EuclideanSpace.proj i).contDiff.contMDiff.comp he
    let T0 : CovariantTensorEvaluation n M 0 := fun p _ => f p
    have hT0 : IsSmoothCovariantTensor T0 := by
      constructor
      · intro p
        exact ⟨MultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace (𝓡 n) p) (f p), fun _ => rfl⟩
      · intro U hU Z hZ
        exact hf.contMDiffOn
    let T1 := D.covariantTensorDerivative T0
    have hT1 : IsSmoothCovariantTensor T1 :=
      M04.isSmoothCovariantTensor_covariantTensorDerivative D hT0
    have hdf (p : M) (w : Fin 1 → TangentSpace (𝓡 n) p) :
        T1 p w = mvfderiv (𝓡 n) f p (w 0) := by
      simp [T1, T0, LeviCivitaData.covariantTensorDerivative]
    have hHessian (p : M) (w : Fin 2 → TangentSpace (𝓡 n) p) :
        D.covariantTensorDerivative T1 p w = D.hessian f p (w 0) (w 1) := by
      have h01 : (Fin.succ 0 : Fin 2) = 1 := by decide
      rw [LeviCivitaData.covariantTensorDerivative]
      simp only [hdf, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Function.update_self, LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
        FiberBundle.extend_apply_self, add_zero, h01]
    have hproj (p : M) (V : TangentSpace (𝓡 n) p) :
        mvfderiv (𝓡 n) f p V =
          EuclideanSpace.proj i (mfderiv (𝓡 n) 𝓘(ℝ, W) e p V) := by
      let L : W →L[ℝ] ℝ := EuclideanSpace.proj i
      change mvfderiv (𝓡 n) (L ∘ e) p V = _
      rw [mvfderiv_comp_apply p L.differentiableAt.mdifferentiableAt
        (he.mdifferentiable (by simp) p) V]
      simpa only [mvfderiv, mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply] using!
        congrArg (fun K : W →L[ℝ] ℝ => K (mfderiv (𝓡 n) 𝓘(ℝ, W) e p V))
          (L.fderiv (x := e p))
    have hscalar := m63HasDerivAt_tensor_pullback D T1 hT1 hgamma
      (fun (_ : Fin 1) s => Y s) (fun _ => hY)
    simpa [hdf, hHessian, hproj, Fin.sum_univ_succ, coordinateHessian, f] using hscalar
  let L : (ι → ℝ) ≃L[ℝ] W :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  have hpi := hasDerivAt_pi.mpr hcoord
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hpi
  convert! h using 1





theorem hasDerivAt_coordinateHessian_pullback {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {gamma : ℝ → M} {x : ℝ}
    (hgamma : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma x)
    (Y Z : (s : ℝ) → TangentSpace (𝓡 n) (gamma s))
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun s => (⟨gamma s, Y s⟩ : TangentBundle (𝓡 n) M)) x)
    (hZ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun s => (⟨gamma s, Z s⟩ : TangentBundle (𝓡 n) M)) x) :
    let T : ι → CovariantTensorEvaluation n M 2 :=
      fun i p w => D.hessian (fun q => e q i) p (w 0) (w 1)
    HasDerivAt (fun s => coordinateHessian D e (gamma s) (Y s) (Z s))
      (WithLp.toLp 2 (fun i => D.covariantTensorDerivative (T i) (gamma x)
          ![curveVelocity gamma x, Y x, Z x]) +
        coordinateHessian D e (gamma x) (rampHorizontalCovariantDerivative D gamma Y x)
          (Z x) +
        coordinateHessian D e (gamma x) (Y x)
          (rampHorizontalCovariantDerivative D gamma Z x)) x := by
  classical
  dsimp only
  let T : ι → CovariantTensorEvaluation n M 2 :=
    fun i p w => D.hessian (fun q => e q i) p (w 0) (w 1)
  have hcoord (i : ι) :
      HasDerivAt (fun s => (coordinateHessian D e (gamma s) (Y s) (Z s)) i)
        ((WithLp.toLp 2 (fun j => D.covariantTensorDerivative (T j) (gamma x)
            ![curveVelocity gamma x, Y x, Z x]) +
          coordinateHessian D e (gamma x) (rampHorizontalCovariantDerivative D gamma Y x)
            (Z x) +
          coordinateHessian D e (gamma x) (Y x)
            (rampHorizontalCovariantDerivative D gamma Z x)) i) x := by
    have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun p => e p i) :=
      (EuclideanSpace.proj i).contDiff.contMDiff.comp he
    have hT : IsSmoothCovariantTensor (T i) := M04.isSmoothCovariantTensor_hessian D hf
    have hfields : ∀ j : Fin 2, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
        (fun s => (⟨gamma s, ![Y, Z] j s⟩ : TangentBundle (𝓡 n) M)) x := by
      intro j
      fin_cases j
      · exact hY
      · exact hZ
    have hscalar := m63HasDerivAt_tensor_pullback D (T i) hT hgamma ![Y, Z] hfields
    have htuple : (fun j : Fin 2 => ![Y, Z] j x) = ![Y x, Z x] := by
      funext j
      fin_cases j <;> rfl
    rw [htuple] at hscalar
    simpa [T, Fin.sum_univ_succ, coordinateHessian, add_assoc] using hscalar
  let L : (ι → ℝ) ≃L[ℝ] W :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  have hpi := hasDerivAt_pi.mpr hcoord
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hpi
  convert! h using 1

end PoincareConjecture.M63
